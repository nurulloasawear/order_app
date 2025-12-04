import json
import os
import pandas as pd
import hashlib
import requests
from datetime import datetime, date, timedelta
import re
import hmac
from io import BytesIO
from typing import Optional, List, Dict
from flask import Flask, request, jsonify, send_from_directory, g
from flask_cors import CORS
from PIL import Image
import logging
import sqlite3
from googleapiclient.discovery import build
import uuid
import threading
import subprocess
import time
import atexit
from fpdf import FPDF


# from auth import require_auth 
# === LOGGING ===
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

# === CONFIG ===
with open("config.json", "r", encoding="utf-8") as f:
    CONFIG = json.load(f)

users = {u["username"]: u for u in CONFIG.get("users", [])}
MAINTENANCE_MODE = False
# Papkalarni yaratish
os.makedirs("temp", exist_ok=True)
os.makedirs("data", exist_ok=True)
os.makedirs("fonts", exist_ok=True)

# === FLASK APP ===
app = Flask(__name__)
CORS(app, origins="*", supports_credentials=True)

# === NGROK CONFIG ===
NGROK_AUTH_TOKEN = CONFIG.get("ngrok_auth_token", "")
NGROK_ENABLED = CONFIG.get("ngrok_enabled", False)
PUBLIC_URL = None


# === DATABASE SETUP ===
class Database:
    def __init__(self, db_path='data/orders.db'):
        self.db_path = db_path
        self._local = threading.local()
        self.init_db()
    
    def get_conn(self):
        if not hasattr(self._local, 'conn'):
            self._local.conn = sqlite3.connect(self.db_path, check_same_thread=False)
            self._local.conn.row_factory = sqlite3.Row
        return self._local.conn
    
    def get_cursor(self):
        return self.get_conn().cursor()
    
    def commit(self):
        if hasattr(self._local, 'conn'):
            self._local.conn.commit()
    
    def close(self):
        if hasattr(self._local, 'conn'):
            self._local.conn.close()
            delattr(self._local, 'conn')
    
    def init_db(self):
        conn = self.get_conn()
        cursor = conn.cursor()
        
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS sessions (
                token_hash TEXT PRIMARY KEY,
                username TEXT NOT NULL,
                expiry REAL NOT NULL,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
        ''')
        
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS decisions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                order_id TEXT NOT NULL,
                decision TEXT NOT NULL,
                warehouse TEXT,
                product_name TEXT,
                quantity INTEGER,
                sku TEXT,
                barcode TEXT,
                username TEXT NOT NULL,
                role TEXT NOT NULL,
                main_save BOOLEAN DEFAULT FALSE,
                timestamp DATETIME DEFAULT CURRENT_TIMESTAMP
            )
        ''')
        
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS reports (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                date TEXT NOT NULL,
                username TEXT NOT NULL,
                accepted INTEGER DEFAULT 0,
                rejected INTEGER DEFAULT 0
            )
        ''')
        # Database init qismiga qo'shamiz:
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS return_status (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                order_id TEXT NOT NULL,
                campaign_id TEXT NOT NULL,
                product_name TEXT,
                sku TEXT,
                quantity INTEGER,
                supplier_status TEXT DEFAULT 'pending', -- 'pending', 'accepted', 'delivered'
                seller_status TEXT DEFAULT 'pending', -- 'pending', 'accepted'
                supplier_username TEXT,
                seller_username TEXT,
                supplier_accepted_at DATETIME,
                supplier_delivered_at DATETIME,
                seller_accepted_at DATETIME,
                created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                UNIQUE(order_id, campaign_id)
            )
        ''')

        cursor.execute('''
            CREATE TABLE IF NOT EXISTS daily_orders (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                order_id TEXT NOT NULL,
                campaign_id TEXT NOT NULL,
                product_name TEXT,
                sku TEXT,
                quantity INTEGER,
                seller_decision TEXT, -- 'yes', 'no'
                supplier_decision TEXT, -- 'yes', 'no', 'alternative'
                seller_username TEXT,
                supplier_username TEXT,
                status TEXT DEFAULT 'pending', -- 'pending', 'seller_accepted', 'supplier_accepted', 'completed'
                alternative_product TEXT,
                created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                updated_at DATETIME DEFAULT CURRENT_TIMESTAMP
            )
        ''')
        
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS processed_orders (
                username TEXT PRIMARY KEY,
                count INTEGER DEFAULT 0
            )
        ''')
        
        # Yangi table admin uchun accepted/returned
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS accepted_returned (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                campaign_id TEXT NOT NULL,
                order_id TEXT NOT NULL,
                product_name TEXT,
                quantity INTEGER,
                status TEXT NOT NULL,  -- 'accepted' or 'returned'
                seller_username TEXT,
                supplier_username TEXT,
                timestamp DATETIME DEFAULT CURRENT_TIMESTAMP
            )
        ''')
        
        conn.commit()

db = Database()

# === REQUEST CONTEXT HANDLING ===
@app.before_request
def before_request():
    g.db = db
    g.cursor = db.get_cursor()

@app.teardown_request
def teardown_request(exception=None):
    if hasattr(g, 'db'):
        g.db.commit()
        if exception:
            g.db.get_conn().rollback()

# === UTILITY FUNCTIONS ===
def sha256_hex(s: str) -> str:
    return hashlib.sha256(s.encode("utf-8")).hexdigest()

def require_auth(roles=None):
    """Decorator: foydalanuvchi avtorizatsiyasini tekshirish"""
    def decorator(f):
        def wrapper(*args, **kwargs):
            auth_header = request.headers.get("Authorization")
            if not auth_header:
                return jsonify({"detail": "Authorization token talab qilinadi"}), 401
            
            token = auth_header.replace('Bearer ', '').strip()
            user = get_user_from_token(token)
            
            if not user:
                return jsonify({"detail": "Yaroqsiz token yoki sessiya muddati tugagan"}), 401
            
            # Rolni tekshirish
            if roles and user.get("role") not in roles:
                return jsonify({"detail": "Ruxsat yo'q"}), 403
            
            g.user = user
            return f(*args, **kwargs)
        wrapper.__name__ = f.__name__
        return wrapper
    return decorator

# === RETURNED ORDERS FOR SUPPLIER ===
@app.route("/api/supplier/returned_orders", methods=["GET"])
@require_auth(["supplier"])
def get_supplier_returned_orders():
    """Supplier uchun qaytarilgan buyurtmalar (Yandex API dan)"""
    user = g.user
    campaign_id = request.args.get("campaign_id", "")
    
    if not campaign_id:
        return jsonify({"detail": "Campaign ID talab qilinadi"}), 400
    
    # Yandex API dan qaytarilgan buyurtmalarni olish
    orders = fetch_yandex_orders(campaign_id, "CANCELLED", user)
    
    if orders is None:
        return jsonify({"detail": "Xato yuz berdi"}), 500
    
    # Bazadagi statuslarni qo'shamiz
    cursor = g.cursor
    for order in orders:
        cursor.execute(
            "SELECT supplier_status, seller_status FROM return_status WHERE order_id = ? AND campaign_id = ?",
            (order["order_id"], campaign_id)
        )
        row = cursor.fetchone()
        if row:
            order["supplier_status"] = row["supplier_status"]
            order["seller_status"] = row["seller_status"]
        else:
            order["supplier_status"] = "pending"
            order["seller_status"] = "pending"
    
    return jsonify(orders)

# === SUPPLIER ACCEPT RETURN ===
@app.route("/api/supplier/accept_return", methods=["POST"])
@require_auth(["supplier"])
def supplier_accept_return():
    """Supplier qaytarilgan buyurtmani qabul qilish"""
    user = g.user
    data = request.json
    order_id = data.get("order_id")
    campaign_id = data.get("campaign_id")
    
    if not order_id or not campaign_id:
        return jsonify({"detail": "Order ID va Campaign ID talab qilinadi"}), 400
    
    cursor = g.cursor
    
    # Statusni yangilash yoki yaratish
    cursor.execute('''
        INSERT OR REPLACE INTO return_status 
        (order_id, campaign_id, supplier_status, supplier_username, supplier_accepted_at)
        VALUES (?, ?, ?, ?, CURRENT_TIMESTAMP)
    ''', (order_id, campaign_id, "accepted", user["username"]))
    
    g.db.commit()
    
    logger.info(f"Supplier {user['username']} qaytarilgan buyurtmani qabul qildi: {order_id}")
    
    return jsonify({
        "status": "success",
        "message": "Qaytarilgan buyurtma qabul qilindi"
    })

# === SUPPLIER DELIVER RETURN ===
@app.route("/api/supplier/deliver_return", methods=["POST"])
@require_auth(["supplier"])
def supplier_deliver_return():
    """Supplier qaytarilgan buyurtmani topshirish"""
    user = g.user
    data = request.json
    order_id = data.get("order_id")
    campaign_id = data.get("campaign_id")
    
    if not order_id or not campaign_id:
        return jsonify({"detail": "Order ID va Campaign ID talab qilinadi"}), 400
    
    cursor = g.cursor
    
    # Statusni yangilash
    cursor.execute('''
        UPDATE return_status 
        SET supplier_status = 'delivered', supplier_delivered_at = CURRENT_TIMESTAMP
        WHERE order_id = ? AND campaign_id = ? AND supplier_username = ?
    ''', (order_id, campaign_id, user["username"]))
    
    if cursor.rowcount == 0:
        return jsonify({"detail": "Buyurtma topilmadi yoki siz qabul qilmagansiz"}), 400
    
    # PDF generatsiya
    try:
        cursor.execute(
            "SELECT product_name, sku, quantity FROM return_status WHERE order_id = ? AND campaign_id = ?",
            (order_id, campaign_id)
        )
        row = cursor.fetchone()
        
        if row:
            items = [{
                "order_id": order_id,
                "product_name": row["product_name"],
                "sku": row["sku"],
                "quantity": row["quantity"]
            }]
            
            date_str = date.today().strftime("%Y-%m-%d")
            pdf_filename = generate_return_pdf(items, "supplier", date_str, user["username"])
            
            logger.info(f"Supplier return PDF yaratildi: {pdf_filename}")
    except Exception as e:
        logger.error(f"PDF yaratishda xato: {e}")
    
    g.db.commit()
    
    logger.info(f"Supplier {user['username']} qaytarilgan buyurtmani topshirdi: {order_id}")
    
    return jsonify({
        "status": "success",
        "message": "Qaytarilgan buyurtma topshirildi",
        "pdf_filename": pdf_filename if 'pdf_filename' in locals() else None
    })

# === SELLER RETURNED ORDERS ===
@app.route("/api/seller/returned_orders", methods=["GET"])
@require_auth(["seller"])
def get_seller_returned_orders():
    """Seller uchun qaytarilgan buyurtmalar (faqat supplier topshirganlar)"""
    user = g.user
    campaign_id = request.args.get("campaign_id", "")
    
    if not campaign_id:
        return jsonify({"detail": "Campaign ID talab qilinadi"}), 400
    
    # Faqat ruxsat etilgan campaign
    assigned = {str(s) for s in user.get("assigned_stores", [])}
    if campaign_id not in assigned:
        return jsonify({"detail": "Ruxsat yo'q"}), 403
    
    cursor = g.cursor
    
    # Supplier tomonidan topshirilgan buyurtmalar
    cursor.execute('''
        SELECT * FROM return_status 
        WHERE campaign_id = ? AND supplier_status = 'delivered'
        ORDER BY supplier_delivered_at DESC
    ''', (campaign_id,))
    
    rows = cursor.fetchall()
    
    # Yandex ma'lumotlarini qo'shamiz
    result = []
    for row in rows:
        order_data = dict(row)
        
        # Yandex API dan qo'shimcha ma'lumot olish
        try:
            yandex_order = fetch_single_order(campaign_id, order_data["order_id"], user)
            if yandex_order:
                order_data.update(yandex_order)
        except:
            pass
        
        result.append(order_data)
    
    return jsonify(result)

# === SELLER ACCEPT RETURN ===
@app.route("/api/seller/accept_return", methods=["POST"])
@require_auth(["seller"])
def seller_accept_return():
    """Seller qaytarilgan buyurtmani qabul qilish"""
    user = g.user
    data = request.json
    order_id = data.get("order_id")
    campaign_id = data.get("campaign_id")
    
    if not order_id or not campaign_id:
        return jsonify({"detail": "Order ID va Campaign ID talab qilinadi"}), 400
    
    cursor = g.cursor
    
    # Statusni yangilash
    cursor.execute('''
        UPDATE return_status 
        SET seller_status = 'accepted', seller_username = ?, seller_accepted_at = CURRENT_TIMESTAMP
        WHERE order_id = ? AND campaign_id = ? AND supplier_status = 'delivered'
    ''', (user["username"], order_id, campaign_id))
    
    if cursor.rowcount == 0:
        return jsonify({"detail": "Buyurtma topilmadi yoki hali topshirilmagan"}), 400
    
    # PDF generatsiya
    try:
        cursor.execute(
            "SELECT product_name, sku, quantity FROM return_status WHERE order_id = ? AND campaign_id = ?",
            (order_id, campaign_id)
        )
        row = cursor.fetchone()
        
        if row:
            items = [{
                "order_id": order_id,
                "product_name": row["product_name"],
                "sku": row["sku"],
                "quantity": row["quantity"]
            }]
            
            date_str = date.today().strftime("%Y-%m-%d")
            pdf_filename = generate_return_pdf(items, "seller", date_str, user["username"])
            
            logger.info(f"Seller return PDF yaratildi: {pdf_filename}")
    except Exception as e:
        logger.error(f"PDF yaratishda xato: {e}")
    
    g.db.commit()
    
    logger.info(f"Seller {user['username']} qaytarilgan buyurtmani qabul qildi: {order_id}")
    
    return jsonify({
        "status": "success",
        "message": "Qaytarilgan buyurtma qabul qilindi",
        "pdf_filename": pdf_filename if 'pdf_filename' in locals() else None
    })

# === DAILY ORDERS MANAGEMENT ===
@app.route("/api/daily_orders/<campaign_id>", methods=["GET"])
@require_auth(["seller", "supplier"])
def get_daily_orders(campaign_id):
    """Kunlik buyurtmalar (seller va supplier uchun)"""
    user = g.user
    
    # Ruxsatni tekshirish
    if user.get("role") == "seller":
        assigned = {str(s) for s in user.get("assigned_stores", [])}
        if str(campaign_id) not in assigned:
            return jsonify({"detail": "Ruxsat yo'q"}), 403
    
    # Yandex API dan bugungi buyurtmalar
    orders = fetch_yandex_orders(campaign_id, "PROCESSING", user)
    
    if orders is None:
        return jsonify({"detail": "Xato yuz berdi"}), 500
    
    # Bazadagi qarorlarni qo'shamiz
    cursor = g.cursor
    for order in orders:
        cursor.execute(
            "SELECT seller_decision, supplier_decision, status FROM daily_orders WHERE order_id = ? AND campaign_id = ?",
            (order["order_id"], campaign_id)
        )
        row = cursor.fetchone()
        if row:
            order["seller_decision"] = row["seller_decision"]
            order["supplier_decision"] = row["supplier_decision"]
            order["status"] = row["status"]
        else:
            order["seller_decision"] = None
            order["supplier_decision"] = None
            order["status"] = "pending"
    
    return jsonify(orders)

# === SAVE DAILY DECISION ===
@app.route("/api/save_daily_decision", methods=["POST"])
@require_auth(["seller", "supplier"])
def save_daily_decision():
    """Kunlik buyurtma bo'yicha qaror saqlash"""
    user = g.user
    data = request.json
    
    order_id = data.get("order_id")
    campaign_id = data.get("campaign_id")
    decision = data.get("decision")  # 'yes', 'no', 'alternative'
    alternative_product = data.get("alternative_product", "")
    
    if not order_id or not campaign_id or not decision:
        return jsonify({"detail": "Barcha maydonlar talab qilinadi"}), 400
    
    cursor = g.cursor
    
    if user["role"] == "seller":
        # Seller qarori
        cursor.execute('''
            INSERT OR REPLACE INTO daily_orders 
            (order_id, campaign_id, seller_decision, seller_username, status, updated_at)
            VALUES (?, ?, ?, ?, 'seller_accepted', CURRENT_TIMESTAMP)
        ''', (order_id, campaign_id, decision, user["username"]))
        
    elif user["role"] == "supplier":
        # Supplier qarori (seller 'no' deb belgilagan bo'lsa ham 'yes' qilishi mumkin)
        cursor.execute('''
            INSERT OR REPLACE INTO daily_orders 
            (order_id, campaign_id, supplier_decision, supplier_username, alternative_product, status, updated_at)
            VALUES (?, ?, ?, ?, ?, 'supplier_accepted', CURRENT_TIMESTAMP)
        ''', (order_id, campaign_id, decision, user["username"], alternative_product))
    
    g.db.commit()
    
    logger.info(f"{user['role']} {user['username']} kunlik buyurtma qarorini saqladi: {order_id}")
    
    return jsonify({
        "status": "success",
        "message": "Qaror saqlandi"
    })

# === OLD ORDERS ===
@app.route("/api/old_orders", methods=["GET"])
@require_auth()
def get_old_orders():
    """Eski buyurtmalar (30 kundan oldingi)"""
    user = g.user
    
    cursor = g.cursor
    
    if user["role"] == "seller":
        # Seller uchun faqat o'z campaignlari
        assigned = user.get("assigned_stores", [])
        placeholders = ','.join(['?'] * len(assigned))
        
        cursor.execute(f'''
            SELECT * FROM decisions 
            WHERE username = ? AND role = 'seller' 
            AND date(timestamp) < date('now', '-30 days')
            AND campaign_id IN ({placeholders})
            ORDER BY timestamp DESC
            LIMIT 100
        ''', [user["username"]] + assigned)
        
    elif user["role"] == "supplier":
        cursor.execute('''
            SELECT * FROM decisions 
            WHERE username = ? AND role = 'supplier' 
            AND date(timestamp) < date('now', '-30 days')
            ORDER BY timestamp DESC
            LIMIT 100
        ''', (user["username"],))
    
    elif user["role"] == "admin":
        cursor.execute('''
            SELECT * FROM decisions 
            WHERE date(timestamp) < date('now', '-30 days')
            ORDER BY timestamp DESC
            LIMIT 200
        ''')
    
    rows = cursor.fetchall()
    
    return jsonify([dict(row) for row in rows])

# === HELPER: Fetch single order ===
def fetch_single_order(campaign_id, order_id, user):
    """Yagona buyurtmani Yandex API dan olish"""
    token = user.get("token") or CONFIG.get("token")
    if not token:
        return None
    
    headers = {
        "Content-Type": "application/json",
        "User-Agent": "NUB/1.0",
        "Accept": "*/*",
        "Api-Key": token
    }
    
    try:
        url = f"https://api.partner.market.yandex.ru/v2/campaigns/{campaign_id}/orders/{order_id}"
        resp = requests.get(url, headers=headers, timeout=30)
        
        if resp.status_code != 200:
            return None
        
        order_data = resp.json()
        
        # Qaytarilgan mahsulot ma'lumotlari
        item = order_data.get("items", [{}])[0] if order_data.get("items") else {}
        
        return {
            "product_name": item.get("offerName", "Noma'lum"),
            "sku": item.get("offerId", item.get("shopSku", "-")),
            "quantity": item.get("count", 1),
            "price": item.get("price", 0) * item.get("count", 1),
            "warehouse": order_data.get("delivery", {}).get("outlet", {}).get("name") or "Noma'lum"
        }
        
    except Exception as e:
        logger.error(f"Yagona buyurtma olishda xato: {e}")
        return None

# === YANGI PDF GENERATOR ===
def generate_return_pdf(items, role, date_str, username):
    """Qaytarilgan buyurtmalar uchun PDF yaratish"""
    pdf = PDF()
    pdf.add_page()
    pdf.add_font("DejaVu", "", "fonts/DejaVuSans.ttf", uni=True)
    pdf.add_font("DejaVu", "B", "fonts/DejaVuSans-Bold.ttf", uni=True)
    
    # Sarlavha
    pdf.set_font("DejaVu", "B", 16)
    if role == "supplier":
        pdf.cell(0, 10, f"QAYTARILGAN BUYURTMALAR - YETKAZIB BERUVCHI", align="C")
    else:
        pdf.cell(0, 10, f"QAYTARILGAN BUYURTMALAR - SOTUVCHI", align="C")
    
    pdf.ln(15)
    pdf.set_font("DejaVu", "", 10)
    pdf.cell(0, 10, f"Sana: {date_str}", 0, 1)
    pdf.cell(0, 10, f"Foydalanuvchi: {username}", 0, 1)
    pdf.ln(10)
    
    # Jadval ustunlari
    headers = ["№", "Mahsulot nomi", "SKU", "Buyurtma ID", "Miqdor", "Holat"]
    widths = [10, 70, 30, 30, 20, 30]
    
    pdf.set_font("DejaVu", "B", 10)
    for i, header in enumerate(headers):
        pdf.cell(widths[i], 10, header, 1, 0, 'C')
    pdf.ln()
    
    # Ma'lumotlar
    pdf.set_font("DejaVu", "", 9)
    for idx, item in enumerate(items, 1):
        status = "Qaytarildi" if role == "supplier" else "Qabul qilindi"
        row = [
            str(idx),
            item.get("product_name", "")[:45],
            item.get("sku", ""),
            item.get("order_id", ""),
            str(item.get("quantity", 0)),
            status
        ]
        
        for i, value in enumerate(row):
            pdf.cell(widths[i], 10, str(value), 1, 0, 'C' if i != 1 else 'L')
        pdf.ln()
    
    # Faylni saqlash
    filename = f"temp/return_{role}_{date_str}_{username}.pdf"
    pdf.output(filename)
    
    return filename
@app.route("/api/admin/toggle_maintenance", methods=["POST"])
@require_auth(["admin"])
def toggle_maintenance():
    """Saytni to'xtatish/yoqish"""
    global MAINTENANCE_MODE
    MAINTENANCE_MODE = not MAINTENANCE_MODE
    
    logger.info(f"Maintenance mode {'activated' if MAINTENANCE_MODE else 'deactivated'} by {g.user['username']}")
    
    return jsonify({
        "status": "success",
        "maintenance_mode": MAINTENANCE_MODE,
        "message": f"Sayt {'to\'xtatildi' if MAINTENANCE_MODE else 'yoqildi'}"
    })
@app.before_request
def check_maintenance():
    """Barcha requestlarni tekshirish"""
    if MAINTENANCE_MODE and request.path.startswith('/api/') and not request.path.endswith('/public_url'):
        # Faqat adminlar maintenance mode da ishlashi mumkin
        auth_header = request.headers.get("Authorization")
        if auth_header:
            token = auth_header.replace('Bearer ', '').strip()
            user = get_user_from_token(token)
            if user and user.get("role") == "admin":
                return None
        
        return jsonify({
            "detail": "Sayt vaqtincha to'xtatilgan. Iltimos, keyinroq qayta urinib ko'ring.",
            "maintenance_mode": True
        }), 423  # 423 - Locked
@app.route("/api/today_orders/<campaign_id>", methods=["GET"])
@require_auth()
def get_today_orders(campaign_id):
    """Bugungi buyurtmalar"""
    user = g.user
    
    if user.get("role") == "seller":
        assigned = {str(s) for s in user.get("assigned_stores", [])}
        if str(campaign_id) not in assigned:
            return jsonify({"detail": "Ruxsat yo'q"}), 403
    
    # Bugungi sanani olish
    today = datetime.now().strftime("%Y-%m-%d")
    
    # Yandex API dan buyurtmalarni olish
    orders = fetch_yandex_orders(campaign_id, "PROCESSING", user)
    if orders is None:
        return jsonify({"detail": "Xato yuz berdi"}), 500
    
    # Real loyihada buyurtmalarni sanasi bo'yicha filtrlash kerak
    # Hozircha barchasini qaytaramiz
    return jsonify(orders)


def get_user_from_token(token: str):
    """Token orqali foydalanuvchini olish"""
    if not token:
        return None
    
    hashed = sha256_hex(token)
    cursor = g.cursor
    
    cursor.execute(
        "SELECT username, expiry FROM sessions WHERE token_hash = ?",
        (hashed,)
    )
    row = cursor.fetchone()
    
    if not row:
        return None
    
    username, expiry = row
    
    # Session muddatini tekshirish
    if datetime.now().timestamp() > expiry:
        cursor.execute("DELETE FROM sessions WHERE token_hash = ?", (hashed,))
        g.db.commit()
        logger.info(f"Session expired for user: {username}")
        return None
    
    return users.get(username)


# === NGROK MANAGEMENT ===
def start_ngrok():
    """Ngrok ni ishga tushirish"""
    global PUBLIC_URL
    
    if not NGROK_ENABLED:
        logger.info("Ngrok o'chirilgan")
        return None
    
    try:
        import pyngrok
        from pyngrok import ngrok
        
        # Pyngrok ni o'rnatish kerak: pip install pyngrok
        
        # Token sozlash
        if NGROK_AUTH_TOKEN:
            ngrok.set_auth_token(NGROK_AUTH_TOKEN)
        
        # Tunnel ochish
        http_tunnel = ngrok.connect(8080, proto="http", bind_tls=True)
        PUBLIC_URL = http_tunnel.public_url
        
        logger.info(f"Ngrok tunnel ochildi: {PUBLIC_URL}")
        logger.info(f"Frontend uchun URL: {PUBLIC_URL}")
        
        return PUBLIC_URL
        
    except ImportError:
        logger.warning("Pyngrok o'rnatilmagan. Qo'lda ngrok ishga tushiring:")
        logger.warning("ngrok http 8080")
        return None
    except Exception as e:
        logger.error(f"Ngrok ishga tushirishda xato: {e}")
        return None

def stop_ngrok():
    """Ngrok ni to'xtatish"""
    try:
        from pyngrok import ngrok
        ngrok.kill()
        logger.info("Ngrok tunnel yopildi")
    except:
        pass

# === NGROK ENDPOINTS ===
@app.route("/api/public_url", methods=["GET"])
def get_public_url():
    """Public URL ni olish"""
    return jsonify({
        "public_url": PUBLIC_URL or "http://localhost:8080",
        "ngrok_enabled": NGROK_ENABLED
    })

# === IMAGE DOWNLOAD ===
def download_image(query: str) -> Optional[str]:
    """Google CSE orqali rasmlarni yuklash"""
    try:
        clean_query = re.sub(r"[^a-zA-Zа-яА-Я0-9\s]", "", query)[:60]
        safe_name = re.sub(r"[^A-Za-z0-9]", "_", clean_query)[:40]
        path = f"temp/{safe_name}.jpg"
        
        if os.path.exists(path):
            return path
        
        cse_config = CONFIG.get("google_cse", {})
        api_key = cse_config.get("api_key")
        cse_id = cse_config.get("cse_id")
        
        if not api_key or not cse_id:
            logger.warning("Google CSE konfiguratsiyasi topilmadi")
            return None
        
        service = build(
            "customsearch", "v1",
            developerKey=api_key,
            cache_discovery=False
        )
        
        search_term = f"{query} -site:tiktok.com filetype:jpg OR filetype:png"
        res = service.cse().list(
            q=search_term,
            cx=cse_id,
            searchType='image',
            num=3,
            safe='high'
        ).execute()
        
        if 'items' not in res:
            return None
        
        image_urls = [item['link'] for item in res['items'][:3]]
        allowed_sites = ["texnomart.uz", "asaxiy.uz", "olcha.uz", "uzum.uz"]
        filtered = [url for url in image_urls if any(site in url for site in allowed_sites)]
        
        if not filtered:
            filtered = image_urls
        
        if not filtered:
            return None
        
        img_resp = requests.get(filtered[0], timeout=15)
        img_resp.raise_for_status()
        
        img = Image.open(BytesIO(img_resp.content)).convert("RGB")
        img.save(path, "JPEG", quality=85)
        return path
        
    except Exception as e:
        logger.warning(f"Rasm yuklashda xato: {e}")
        return None

# === AUTHENTICATION ENDPOINTS ===
@app.route("/api/login", methods=["POST"])
def login():
    """Login endpoint"""
    data = request.form
    username = data.get("username")
    password = data.get("password")
    
    if not username or not password:
        return jsonify({"detail": "Login va parol talab qilinadi"}), 400
    
    user = users.get(username)
    if not user:
        return jsonify({"detail": "Foydalanuvchi topilmadi"}), 401
    
    provided_hash = sha256_hex(password)
    stored_hash = user.get("password_hash", "")
    
    if not hmac.compare_digest(provided_hash, stored_hash):
        return jsonify({"detail": "Noto'g'ri parol"}), 401
    
    # Session yaratish
    session_token = str(uuid.uuid4())
    hashed_session = sha256_hex(session_token)
    expiry = datetime.now().timestamp() + (3600 * 8)
    print(user.get("assigned_stores", []))
    cursor = g.cursor
    cursor.execute(
        "INSERT OR REPLACE INTO sessions (token_hash, username, expiry) VALUES (?, ?, ?)",
        (hashed_session, username, expiry)
    )
    g.db.commit()
    
    logger.info(f"User logged in: {username}")
    
    return jsonify({
        "username": user["username"],
        "token": session_token,
        "role": user.get("role", "seller"),
        "is_admin": user.get("role") == "admin",
        "assigned_stores": user.get("assigned_stores", []),
        "public_url": PUBLIC_URL or "http://localhost:8080"  # <- Yangi qator
    })

@app.route("/api/logout", methods=["POST"])
@require_auth()
def logout():
    """Logout endpoint"""
    auth_header = request.headers.get("Authorization")
    token = auth_header.replace('Bearer ', '').strip()
    hashed = sha256_hex(token)
    
    cursor = g.cursor
    cursor.execute("DELETE FROM sessions WHERE token_hash = ?", (hashed,))
    g.db.commit()
    
    return jsonify({"status": "logged out"})

# === CAMPAIGNS ===
@app.route("/api/campaigns", methods=["GET"])
@require_auth()
def get_campaigns():
    """Campaigns ro'yxatini olish"""
    user = g.user
    token = user.get("token") or CONFIG.get("token")
    
    if not token:
        return jsonify({"detail": "Token topilmadi"}), 400
    
    headers = {
        "Content-Type": "application/json",
        "User-Agent": "NUB/1.0",
        "Accept": "*/*",
        "Api-Key": token
    }
    
    all_campaigns = []
    page = 1
    
    try:
        while True:
            url = "https://api.partner.market.yandex.ru/v2/campaigns"
            params = {"page": page, "pageSize": 50}
            
            resp = requests.get(url, headers=headers, params=params, timeout=30)
            if resp.status_code != 200:
                logger.error(f"Yandex API xatosi: {resp.status_code}")
                break
            
            data = resp.json()
            campaigns = data.get("campaigns", [])
            if not campaigns:
                break
            
            all_campaigns.extend(campaigns)
            
            pager = data.get("pager", {})
            if page >= pager.get("pagesCount", 1):
                break
            page += 1
        
        # Rolga qarab filtrlash
        if user.get("role") == "seller":
            assigned = {str(s) for s in user.get("assigned_stores", [])}
            result = [
                {"id": str(c["id"]), "name": c.get("domain", f"Do'kon {c['id']}")}
                for c in all_campaigns
                if str(c["id"]) in assigned
            ]
        elif user.get("role") == "admin":
            result = [
                {"id": str(c["id"]), "name": c.get("domain", f"Do'kon {c['id']}")}
                for c in all_campaigns
            ]
        elif user.get("role") == "supplier":
            # Supplier uchun barcha kampaniyalarni ko'rsatamiz
            result = [
                {"id": str(c["id"]), "name": c.get("domain", f"Do'kon {c['id']}")}
                for c in all_campaigns
            ]
        else:
            result = []
        
        return jsonify(result)
        
    except Exception as e:
        logger.error(f"Campaigns olishda xato: {e}")
        return jsonify({"detail": f"Xato: {str(e)}"}), 500

@app.route("/api/update_backend_url", methods=["POST"])
@require_auth(["admin"])
def update_backend_url():
    """Barcha foydalanuvchilar uchun backend URL ni yangilash"""
    data = request.json
    new_url = data.get("url", "")
    
    if not new_url:
        return jsonify({"detail": "URL talab qilinadi"}), 400
    
    # Config faylini yangilash
    CONFIG["backend_url"] = new_url
    with open("config.json", "w", encoding="utf-8") as f:
        json.dump(CONFIG, f, ensure_ascii=False, indent=2)
    
    # Barcha sessiyalarga yangi URL ni saqlash (agar kerak bo'lsa)
    cursor = g.cursor
    cursor.execute("UPDATE sessions SET metadata = ?", (json.dumps({"backend_url": new_url}),))
    g.db.commit()
    
    logger.info(f"Backend URL yangilandi: {new_url}")
    
    return jsonify({
        "status": "success",
        "message": f"Backend URL yangilandi: {new_url}",
        "public_url": PUBLIC_URL
    })

# === YANDEX API HELPER ===
def fetch_yandex_orders(campaign_id, status="PROCESSING", user=None):
    """Yandex API dan buyurtmalarni olish"""
    if not user:
        user = g.user
    
    token = user.get("token") or CONFIG.get("token")
    if not token:
        return None
    print(campaign_id)
    headers = {
        "Content-Type": "application/json",
        "User-Agent": "NUB/1.0",
        "Accept": "*/*",
        "Api-Key": token
    }
    
    try:
        url = f"https://api.partner.market.yandex.ru/v2/campaigns/{campaign_id}/orders"
        params = {"status": status}
        
        resp = requests.get(url, headers=headers, params=params, timeout=30)
        if resp.status_code != 200:
            logger.error(f"Yandex orders API xatosi: {resp.text}")
            return None
        
        orders_data = resp.json().get("orders", [])
        result = []
        
        for order in orders_data:
            warehouse = order.get("delivery", {}).get("outlet", {}).get("name") or "Noma'lum"
            
            for item in order.get("items", []):
                product_data = {
                    "order_id": str(order["id"]),
                    "product_name": item.get("offerName", "Noma'lum"),
                    "sku": item.get("offerId", item.get("shopSku", "-")),
                    "quantity": item.get("count", 1),
                    "warehouse": warehouse,
                    "barcode": item.get("barcode", "-"),
                    "price": item.get("price", 0) * item.get("count", 1)
                }
                
                img_path = download_image(f"{product_data['product_name']} {product_data['sku']}")
                if img_path:
                    product_data["image"] = f"/temp/{os.path.basename(img_path)}"
                
                result.append(product_data)
        
        return result
        
    except Exception as e:
        logger.error(f"Buyurtmalarni olishda xato: {e}")
        return None

# === ORDERS ENDPOINTS ===
@app.route("/api/orders/<campaign_id>", methods=["GET"])
@require_auth()
def get_orders(campaign_id):
    """Buyurtmalarni olish"""
    user = g.user
    
    # Campaign ID ni tekshirish
    if user.get("role") == "seller":
        assigned = {str(s) for s in user.get("assigned_stores", [])}
        if str(campaign_id) not in assigned:
            return jsonify({"detail": "Bu campaign ga ruxsatingiz yo'q"}), 403
    
    orders = fetch_yandex_orders(campaign_id, "PROCESSING", user)
    if orders is None:
        return jsonify({"detail": "Buyurtmalarni olishda xato"}), 500
    
    return jsonify(orders)

@app.route("/api/canceled_orders/<campaign_id>", methods=["GET"])
@require_auth()
def get_canceled_orders(campaign_id):
    """Bekor qilingan buyurtmalar"""
    user = g.user
    
    if user.get("role") == "seller":
        assigned = {str(s) for s in user.get("assigned_stores", [])}
        if str(campaign_id) not in assigned:
            return jsonify({"detail": "Ruxsat yo'q"}), 403
        
        # Seller uchun faqat o'z campaign_id si bo'yicha qaytarilgan buyurtmalar
        cursor = g.cursor
        cursor.execute('''
            SELECT d.* FROM decisions d 
            JOIN accepted_returned ar ON d.order_id = ar.order_id 
            WHERE ar.campaign_id = ? AND d.role = 'supplier' AND d.decision = 'yes'
        ''', (campaign_id,))
        rows = cursor.fetchall()
        orders = [dict(row) for row in rows]
    else:
        # Supplier/admin uchun Yandexdan bekor qilinganlar
        orders = fetch_yandex_orders(campaign_id, "CANCELLED", user)
    
    if orders is None:
        return jsonify({"detail": "Xato yuz berdi"}), 500
    
    return jsonify(orders)

# === STATISTICS ===
@app.route("/api/order_stats", methods=["GET"])
@require_auth()
def get_order_stats():
    """Buyurtma statistikasi"""
    user = g.user
    token = user.get("token") or CONFIG.get("token")
    
    if not token:
        return jsonify({"detail": "Token topilmadi"}), 400
    
    headers = {
        "Content-Type": "application/json",
        "User-Agent": "NUB/1.0",
        "Accept": "*/*",
        "Api-Key": token
    }
    
    # Campaigns ro'yxatini olish
    campaigns_response = get_campaigns()
    if isinstance(campaigns_response, tuple):
        return campaigns_response
    
    campaigns_data = campaigns_response.get_json()
    if not isinstance(campaigns_data, list):
        return jsonify({"detail": "Campaigns ma'lumotlari noto'g'ri"}), 500
    
    campaign_ids = [c["id"] for c in campaigns_data]
    
    stats = {
        "assembly": 0,
        "shipments": 0,
        "delivery": 0,
        "delivered": 0,
        "canceled": 0
    }
    
    for campaign_id in campaign_ids:
        try:
            url = f"https://api.partner.market.yandex.ru/v2/campaigns/{campaign_id}/stats/orders.json"
            params = {"groupBy": "STATUS"}
            
            resp = requests.get(url, headers=headers, params=params, timeout=30)
            if resp.status_code != 200:
                continue
            
            groups = resp.json().get("groups", [])
            for group in groups:
                status = group.get("status")
                count = group.get("ordersCount", 0)
                
                if status == "PROCESSING":
                    stats["assembly"] += count
                    stats["shipments"] += count
                elif status == "DELIVERY":
                    stats["delivery"] += count
                elif status == "DELIVERED":
                    stats["delivered"] += count
                elif status == "CANCELLED":
                    stats["canceled"] += count
                    
        except Exception as e:
            logger.error(f"Campaign {campaign_id} statistikasida xato: {e}")
            continue
    
    return jsonify(stats)

@app.route("/api/sales_chart_data", methods=["GET"])
@require_auth()
def get_sales_chart_data():
    """Sotuv statistikasi uchun ma'lumot"""
    user = g.user
    token = user.get("token") or CONFIG.get("token")
    filter_type = request.args.get("filter", "7days")
    
    if not token:
        return jsonify({"detail": "Token topilmadi"}), 400
    
    # Vaqt oralig'ini aniqlash
    today = date.today()
    
    if filter_type == "7days":
        from_date = today - timedelta(days=7)
        days = 8
    elif filter_type == "month":
        from_date = today.replace(day=1)
        days = (today - from_date).days + 1
    elif filter_type == "october":
        from_date = date(today.year, 10, 1)
        days = (date(today.year, 10, 31) - from_date).days + 1
    else:
        return jsonify({"detail": "Noto'g'ri filter"}), 400
    
    headers = {
        "Content-Type": "application/json",
        "User-Agent": "NUB/1.0",
        "Accept": "*/*",
        "Api-Key": token
    }
    
    # Campaigns ro'yxatini olish
    campaigns_response = get_campaigns()
    if isinstance(campaigns_response, tuple):
        return campaigns_response
    
    campaigns_data = campaigns_response.get_json()
    if not isinstance(campaigns_data, list):
        return jsonify({"detail": "Campaigns ma'lumotlari noto'g'ri"}), 500
    
    campaign_ids = [c["id"] for c in campaigns_data]
    
    # Kundalik sotuvlar
    daily_sums = [0] * days
    labels = [(from_date + timedelta(d)).strftime("%Y-%m-%d") for d in range(days)]
    
    for campaign_id in campaign_ids:
        try:
            url = f"https://api.partner.market.yandex.ru/v2/campaigns/{campaign_id}/stats/orders.json"
            params = {
                "fromDate": from_date.strftime("%Y-%m-%d"),
                "toDate": today.strftime("%Y-%m-%d"),
                "groupBy": "DAY"
            }
            
            resp = requests.get(url, headers=headers, params=params, timeout=30)
            if resp.status_code != 200:
                continue
            
            groups = resp.json().get("groups", [])
            for group in groups:
                day_str = group.get("date")
                if not day_str:
                    continue
                
                try:
                    day_date = date.fromisoformat(day_str)
                    day_index = (day_date - from_date).days
                    
                    if 0 <= day_index < days:
                        for order in group.get("orders", []):
                            if order.get("status") == "DELIVERED":
                                order_sum = sum(
                                    item.get("price", 0) * item.get("count", 1) 
                                    for item in order.get("items", [])
                                )
                                daily_sums[day_index] += order_sum
                except ValueError:
                    continue
                    
        except Exception as e:
            logger.error(f"Chart data olishda xato: {e}")
            continue
    
    return jsonify({"labels": labels, "data": daily_sums})

# === ADMIN ENDPOINTS ===
@app.route("/api/admin/users", methods=["GET"])
@require_auth(["admin"])
def admin_get_users():
    """Barcha foydalanuvchilar ro'yxati"""
    cursor = g.cursor
    cursor.execute("SELECT count FROM processed_orders WHERE username = ?", (g.user["username"],))
    processed_row = cursor.fetchone()
    processed_count = processed_row[0] if processed_row else 0
    
    users_list = []
    for u in CONFIG.get("users", []):
        cursor.execute("SELECT count FROM processed_orders WHERE username = ?", (u["username"],))
        row = cursor.fetchone()
        
        users_list.append({
            "username": u["username"],
            "role": u.get("role", "seller"),
            "assigned_stores": u.get("assigned_stores", []),
            "token": u.get("token", ""),
            "processed_orders": row[0] if row else 0
        })
    
    return jsonify(users_list)

@app.route("/api/admin/create_user", methods=["POST"])
@require_auth(["admin"])
def admin_create_user():
    """Yangi foydalanuvchi yaratish"""
    data = request.form
    username = data.get("username")
    password = data.get("password")
    role = data.get("role")
    
    if not username or not password or not role:
        return jsonify({"detail": "Username, password va role talab qilinadi"}), 400
    
    if username in users:
        return jsonify({"detail": "Foydalanuvchi allaqachon mavjud"}), 400
    
    assigned_stores = []
    if role == "seller":
        stores_str = data.get("assigned_stores", "")
        assigned_stores = [x.strip() for x in stores_str.split(",") if x.strip()]
    
    new_user = {
        "username": username,
        "password_hash": sha256_hex(password),
        "token": data.get("token", ""),
        "role": role,
        "assigned_stores": assigned_stores
    }
    
    users[username] = new_user
    CONFIG["users"].append(new_user)
    
    with open("config.json", "w", encoding="utf-8") as f:
        json.dump(CONFIG, f, ensure_ascii=False, indent=2)
    
    return jsonify({"status": "created"})

@app.route("/api/admin/update_user", methods=["POST"])
@require_auth(["admin"])
def admin_update_user():
    """Foydalanuvchini yangilash"""
    data = request.form
    username = data.get("username")
    
    if not username:
        return jsonify({"detail": "Username talab qilinadi"}), 400
    
    user = users.get(username)
    if not user:
        return jsonify({"detail": "Foydalanuvchi topilmadi"}), 404
    
    # Yangilash
    if data.get("password"):
        user["password_hash"] = sha256_hex(data.get("password"))
    
    if data.get("token"):
        user["token"] = data.get("token")
    
    if data.get("role"):
        user["role"] = data.get("role")
        
        if data.get("role") == "seller":
            stores_str = data.get("assigned_stores", "")
            user["assigned_stores"] = [x.strip() for x in stores_str.split(",") if x.strip()]
        else:
            user["assigned_stores"] = []
    
    # Config faylini yangilash
    for i, u in enumerate(CONFIG["users"]):
        if u["username"] == username:
            CONFIG["users"][i] = user
            break
    
    with open("config.json", "w", encoding="utf-8") as f:
        json.dump(CONFIG, f, ensure_ascii=False, indent=2)
    
    return jsonify({"status": "updated"})

# Yangi: Admin style update
@app.route("/api/admin/update_styles", methods=["POST"])
@require_auth(["admin"])
def admin_update_styles():
    data = request.json
    CONFIG["styles"] = data.get("styles", {})
    with open("config.json", "w", encoding="utf-8") as f:
        json.dump(CONFIG, f, ensure_ascii=False, indent=2)
    return jsonify({"status": "styles updated"})

# Yangi: Admin accepted/returned
@app.route("/api/admin/accepted_returned/<campaign_id>", methods=["GET"])
@require_auth(["admin"])
def admin_accepted_returned(campaign_id):
    cursor = g.cursor
    cursor.execute("SELECT * FROM accepted_returned WHERE campaign_id = ?", (campaign_id,))
    rows = cursor.fetchall()
    return jsonify([dict(row) for row in rows])

# === SUPPLIER ORDERS ===
@app.route("/api/supplier/orders", methods=["GET"])
@require_auth(["supplier"])
def supplier_get_orders():
    """Supplier uchun buyurtmalar"""
    cursor = g.cursor
    cursor.execute(
        "SELECT * FROM decisions WHERE role = 'seller' AND main_save = 0 AND decision = 'yes'"
    )
    rows = cursor.fetchall()
    
    result = []
    for row in rows:
        result.append({
            "id": row[0],
            "order_id": row[1],
            "decision": row[2],
            "warehouse": row[3],
            "product_name": row[4],
            "quantity": row[5],
            "sku": row[6],
            "barcode": row[7],
            "username": row[8]
        })
    
    return jsonify(result)

# === SAVE DECISIONS ===
@app.route("/api/save", methods=["POST"])
@require_auth(["seller", "supplier"])
def save_decisions():
    """Qarorlarni saqlash"""
    user = g.user
    data = request.json
    
    if not data:
        return jsonify({"detail": "Ma'lumot talab qilinadi"}), 400
    
    decisions = data.get("decisions", [])
    temp_save = data.get("temp_save", False)
    
    if not decisions:
        return jsonify({"detail": "Hech qanday qaror berilmagan"}), 400
    
    cursor = g.cursor
    
    # Ma'lumotlarni bazaga saqlash
    for d in decisions:
        cursor.execute('''
            INSERT INTO decisions 
            (order_id, decision, warehouse, product_name, quantity, sku, barcode, username, role, main_save)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        ''', (
            d.get("order_id"),
            d.get("decision"),
            d.get("warehouse", ""),
            d.get("product_name", ""),
            d.get("quantity", 1),
            d.get("sku", ""),
            d.get("barcode", ""),
            user["username"],
            user["role"],
            0 if temp_save else 1
        ))
        
        # Accepted/returned saqlash
        status = 'accepted' if d.get("decision") == "yes" else 'returned'
        cursor.execute('''
            INSERT INTO accepted_returned 
            (campaign_id, order_id, product_name, quantity, status, seller_username, supplier_username)
            VALUES (?, ?, ?, ?, ?, ?, ?)
        ''', (
            d.get("campaign_id", ""),
            d.get("order_id"),
            d.get("product_name", ""),
            d.get("quantity", 1),
            status,
            user["username"] if user["role"] == "seller" else "",
            user["username"] if user["role"] == "supplier" else ""
        ))
    
    # Processed orders hisobini yangilash
    cursor.execute(
        "INSERT OR REPLACE INTO processed_orders (username, count) VALUES (?, COALESCE((SELECT count FROM processed_orders WHERE username = ?), 0) + ?)",
        (user["username"], user["username"], len(decisions))
    )
    
    g.db.commit()
    
    # PDF yaratish (agar temp_save bo'lmasa)
    pdf_filenames = []
    if not temp_save:
        try:
            date_str = date.today().strftime("%Y-%m-%d")
            
            # "Yes" qarorlari uchun PDF
            yes_decisions = [d for d in decisions if d.get("decision") == "yes"]
            if yes_decisions:
                pdf_yes = generate_pdf(yes_decisions, True, date_str, user["username"])
                pdf_filenames.append(os.path.basename(pdf_yes))
            
            # "No" qarorlari uchun PDF
            no_decisions = [d for d in decisions if d.get("decision") == "no"]
            if no_decisions:
                pdf_no = generate_pdf(no_decisions, False, date_str, user["username"])
                pdf_filenames.append(os.path.basename(pdf_no))
                
            # Qaytarilgan uchun alohida PDF
            returned_decisions = [d for d in decisions if d.get("decision") == "no" and user["role"] == "supplier"]
            if returned_decisions:
                pdf_returned = generate_returned_pdf(returned_decisions, date_str, user["username"])
                pdf_filenames.append(os.path.basename(pdf_returned))
                
        except Exception as e:
            logger.error(f"PDF yaratishda xato: {e}")
    
    return jsonify({
        "status": "saved",
        "pdf_filename": pdf_filenames[0] if pdf_filenames else "",
        "files": pdf_filenames
    })

# === PDF GENERATION ===
class PDF(FPDF):
    """PDF yaratish klassi"""
    def header(self):
        # Logolarni qo'shish
        try:
            if os.path.exists("fineok_logo.jpg"):
                self.image("fineok_logo.jpg", 10, 10, 40, 20)
        except:
            pass
        
        try:
            if os.path.exists("spphone_logo.png"):
                self.image("spphone_logo.png", self.w - 50, 10, 40, 20)
        except:
            pass
        self.add_font("DejaVu", "", "fonts/DejaVuSans.ttf", uni=True)
        self.add_font("DejaVu", "B", "fonts/DejaVuSans-Bold.ttf", uni=True)
        self.set_font("DejaVu", "B", 12)
        self.ln(25)
        self.cell(0, 10, f"НАКЛАДНАЯ № ____        ОТ {date.today().strftime('%d.%m.%Y')}", align="C")
        self.ln(5)
    
    def footer(self):
        self.add_font("DejaVu", "", "fonts/DejaVuSans.ttf", uni=True)
        self.add_font("DejaVu", "B", "fonts/DejaVuSans-Bold.ttf", uni=True) 
        self.set_y(-35)
        self.set_font("DejaVu", "", 9)
        self.cell(90, 6, "От FineOk: ________________________________", 0, 0, "L")
        self.cell(10)
        self.cell(90, 6, "От SP Phone: ________________________________", 0, 1, "L")
        self.cell(90, 6, "(Ф.И.О., подпись)", 0, 0, "L")
        self.cell(10)
        self.cell(90, 6, "(Ф.И.О., подпись)", 0, 1, "L")

def generate_pdf(items, is_positive, date_str, username):
    """PDF fayl yaratish"""
    pdf = PDF()
    pdf.add_page()
    pdf.add_font("DejaVu", "", "fonts/DejaVuSans.ttf", uni=True)
    pdf.add_font("DejaVu", "B", "fonts/DejaVuSans-Bold.ttf", uni=True)
    
    # Agar "No" qarorlari bo'lsa, ogohlantirish qo'shish
    if not is_positive:
        tomorrow = (datetime.strptime(date_str, "%Y-%m-%d") + timedelta(days=1)).strftime("%d.%m.%Y")
        pdf.set_font("DejaVu", "B", 16)
        pdf.set_text_color(200, 0, 0)
        pdf.cell(0, 12, f"Ҳурматли {username}!", align="C")
        pdf.ln()
        
        pdf.set_font("DejaVu", "", 10)
        pdf.set_text_color(0, 0, 0)
        pdf.multi_cell(0, 6, 
            f"{tomorrow} йилдаги буюртма бўйича кўрсатилган товарлар сизнинг омборингизда "
            f"мавжуд бўлмаганлиги сабабли тақдим этилмади. Илтимос, ушбу товарларни "
            f"бошқа омборингиздан етказиб беришни ташкил этинг."
        )
        pdf.ln(5)
    
    # Jadval ustunlari
    headers = ["№", "Наименование товара", "SKU", "Номер заказа", "Штрихкод", "Кол-во", "Статус"]
    widths = [10, 70, 25, 25, 25, 15, 20]
    
    # Jadval sarlavhasi
    pdf.set_font("DejaVu", "B", 10)
    for i, header in enumerate(headers):
        pdf.cell(widths[i], 10, header, 1, 0, 'C')
    pdf.ln()
    
    # Ma'lumotlar
    pdf.set_font("DejaVu", "", 9)
    for idx, item in enumerate(items, 1):
        row = [
            str(idx),
            item.get("product_name", "")[:50],
            item.get("sku", ""),
            item.get("order_id", ""),
            item.get("barcode", ""),
            str(item.get("quantity", 0)),
            "OK" if is_positive else "NO"
        ]
        
        for i, value in enumerate(row):
            pdf.cell(widths[i], 10, str(value), 1, 0, 'C' if i != 1 else 'L')
        pdf.ln()
    
    # Faylni saqlash
    filename = f"temp/{'positive' if is_positive else 'negative'}_report_{date_str}_{username}.pdf"
    pdf.output(filename)
    
    return filename

# Yangi: Qaytarilgan uchun PDF
def generate_returned_pdf(items, date_str, username):
    pdf = PDF()
    pdf.add_page()
    pdf.set_font("DejaVu", "B", 16)
    pdf.set_text_color(200, 0, 0)
    pdf.cell(0, 12, f"Qaytarilgan buyurtmalar: {username}", align="C")
    pdf.ln()
    
    # Jadval
    headers = ["№", "Товар", "SKU", "Заказ", "Штрихкод", "Кол-во"]
    widths = [10, 70, 25, 25, 25, 15]
    
    pdf.set_font("Arial", "B", 10)
    for i, header in enumerate(headers):
        pdf.cell(widths[i], 10, header, 1, 0, 'C')
    pdf.ln()
    
    pdf.set_font("DejaVu", "", 9)
    for idx, item in enumerate(items, 1):
        row = [
            str(idx),
            item.get("product_name", "")[:50],
            item.get("sku", ""),
            item.get("order_id", ""),
            item.get("barcode", ""),
            str(item.get("quantity", 0))
        ]
        
        for i, value in enumerate(row):
            pdf.cell(widths[i], 10, str(value), 1, 0, 'C' if i != 1 else 'L')
        pdf.ln()
    
    filename = f"temp/returned_report_{date_str}_{username}.pdf"
    pdf.output(filename)
    
    return filename

# === PDF DOWNLOAD ===
@app.route("/api/pdf/<filename>", methods=["GET"])
# @require_auth()
def get_pdf(filename):
    """PDF faylini yuklash"""
    try:
        return send_from_directory("temp", filename, as_attachment=True)
    except:
        return jsonify({"detail": "Fayl topilmadi"}), 404

# === EXCEL REPORT ===
@app.route("/api/excel", methods=["GET"])
@require_auth(["admin"])
def get_excel_report():
    """Excel hisobotini yuklash"""
    cursor = g.cursor
    cursor.execute("SELECT * FROM reports")
    rows = cursor.fetchall()
    
    if not rows:
        return jsonify({"detail": "Hisobot hali yaratilmagan"}), 404
    
    # DataFrame yaratish
    df = pd.DataFrame(rows, columns=['id', 'date', 'username', 'accepted', 'rejected'])
    excel_path = "data/excel_report.xlsx"
    df.to_excel(excel_path, index=False)
    
    return send_from_directory("data", "excel_report.xlsx", as_attachment=True)

# === STATIC FILES ===
@app.route('/temp/<path:filename>')
def serve_temp(filename):
    """Temp fayllarni serv qilish"""
    return send_from_directory('temp', filename)

@app.route('/')
def serve_index():
    """Asosiy sahifa"""
    return send_from_directory('.', 'dashboard.html')

# === CLEANUP ===
def cleanup_temp():
    """Eski temp fayllarni o'chirish"""
    try:
        for file in os.listdir("temp"):
            file_path = os.path.join("temp", file)
            if os.path.isfile(file_path):
                file_age = datetime.now().timestamp() - os.path.getctime(file_path)
                if file_age > 259200:  # 3 kun
                    os.remove(file_path)
    except Exception as e:
        logger.error(f"Temp tozalashda xato: {e}")

# === MAIN ===
if __name__ == "__main__":
    print("=" * 70)
    print("GadgetPro Dashboard Backend - Ngrok versiyasi")
    print("=" * 70)
    
    # Temp papkasini tozalash
    cleanup_temp()
    
    # Ngrok ni ishga tushirish
    public_url = start_ngrok()
    
    # Exit handler - ngrok ni to'xtatish
    atexit.register(stop_ngrok)
    
    if public_url:
        print(f"✅ Ngrok tunnel ochildi")
        print(f"🌐 Public URL: {public_url}")
        print(f"📱 Frontend uchun: {public_url}")
        print(f"🔗 API endpoint: {public_url}/api")
        print("=" * 70)
    else:
        print("⚠️  Ngrok ishga tushirilmadi")
        print("🔗 Local URL: http://localhost:8080")
        print("🔗 API endpoint: http://localhost:8080/api")
        print("=" * 70)
        print("Agar ngrok kerak bo'lsa, alohida terminalda quyidagi buyruqni ishga tushiring:")
        print("ngrok http 8080")
        print("=" * 70)
    
    # Serverni ishga tushirish
    try:
        app.run(
            host="0.0.0.0",
            port=8080,
            debug=False,
            threaded=True,
            use_reloader=False
        )
    except KeyboardInterrupt:
        print("\nServerni to'xtatish...")
        stop_ngrok()
        print("Dastur to'xtatildi.")