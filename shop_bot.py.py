import html
import logging
import os
import sqlite3
import threading
import time
import json
import uuid
import random
import re
from datetime import datetime
from io import BytesIO
from typing import Dict, List, Tuple
from functools import wraps
from collections import defaultdict

import qrcode
import requests

try:
    from reportlab.lib.pagesizes import A4
    from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, Image
    from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
    from reportlab.lib.units import mm
    from reportlab.lib import colors
    PDF_AVAILABLE = True
except ImportError:
    PDF_AVAILABLE = False

from telebot import TeleBot
from telebot.types import (
    InlineKeyboardMarkup, InlineKeyboardButton,
    ReplyKeyboardMarkup, KeyboardButton
)

# ==================== CONFIGURATION (CHANGE THESE) ====================
BOT_TOKEN = "YOUR_BOT_TOKEN_HERE"          # Get from @BotFather
OWNER_ID = 123456789                       # Your Telegram ID

# Admins (add IDs of people who can manage the shop)
ADMIN_IDS = [OWNER_ID]                     # Add more: 987654321, ...

# Shop info
SHOP_NAME = "My Shop"
CONTACT_TELEGRAM = "https://t.me/yourusername"
CONTACT_PHONE = "+1234567890"

# Delivery
DELIVERY_TIMEFRAME_MIN_DAYS = 2
DELIVERY_TIMEFRAME_MAX_DAYS = 5

# Payment (manual bank transfer)
MANUAL_PAYMENT_BANK_NAME = "Your Bank"
MANUAL_PAYMENT_ACCOUNT_NAME = "Your Name"
MANUAL_PAYMENT_ACCOUNT_NUMBER = "123456789"

# KHQR (optional – you can keep as is or set to empty)
KHPAY_API_KEY = "#replace with khpay api"
KHPAY_BASE_URL = "https://khpay.site/api/v1"
KHPAY_TIMEOUT = 30

# Paths
DB_PATH = "shop.db"
IMAGES_DIR = "product_images"
RECEIPTS_DIR = "receipts"
BACKUPS_DIR = "backups"
LOGO_DIR = "store_logo"

for d in [IMAGES_DIR, RECEIPTS_DIR, BACKUPS_DIR, LOGO_DIR]:
    os.makedirs(d, exist_ok=True)

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

bot = TeleBot(BOT_TOKEN, parse_mode='HTML')
user_states = {}
active_payments = {}
pending_locations = {}
pending_receipts = {}

ORDER_STATUSES = {
    'pending': '⏳ Pending',
    'processing': '🔄 Processing',
    'shipped': '🚚 Shipped',
    'delivered': '✅ Delivered',
    'cancelled': '❌ Cancelled',
    'awaiting_receipt': '📸 Awaiting Receipt'
}

# ==================== DATABASE ====================
def init_db():
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute('''CREATE TABLE IF NOT EXISTS users (
        user_id INTEGER PRIMARY KEY,
        username TEXT, first_name TEXT, phone TEXT,
        joined_date TEXT, last_active TEXT,
        total_orders INTEGER DEFAULT 0, total_spent REAL DEFAULT 0,
        is_admin INTEGER DEFAULT 0, language TEXT DEFAULT 'en')''')
    c.execute('''CREATE TABLE IF NOT EXISTS categories (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        name TEXT UNIQUE, emoji TEXT, description TEXT, sort_order INTEGER)''')
    c.execute('''CREATE TABLE IF NOT EXISTS products (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        unique_id TEXT UNIQUE, name TEXT, category TEXT,
        price REAL, description TEXT, image_file_id TEXT,
        stock INTEGER DEFAULT -1, is_active INTEGER DEFAULT 1,
        created_at TEXT, avg_rating REAL DEFAULT 0, total_reviews INTEGER DEFAULT 0)''')
    c.execute('''CREATE TABLE IF NOT EXISTS orders (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        order_number TEXT UNIQUE, user_id INTEGER,
        product_name TEXT, total_amount REAL,
        customer_phone TEXT, customer_name TEXT,
        payment_status TEXT, order_status TEXT,
        khpay_qr_string TEXT, notes TEXT,
        tracking_updates TEXT, created_at TEXT)''')
    c.execute('''CREATE TABLE IF NOT EXISTS cart (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER, product_id INTEGER,
        product_name TEXT, product_price REAL, quantity INTEGER)''')
    c.execute('''CREATE TABLE IF NOT EXISTS product_reviews (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        product_id INTEGER, user_id INTEGER, username TEXT,
        rating INTEGER, review_text TEXT, created_at TEXT)''')
    c.execute('''CREATE TABLE IF NOT EXISTS stock_subscriptions (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER, product_id INTEGER, product_name TEXT,
        is_active INTEGER DEFAULT 1)''')
    c.execute('''CREATE TABLE IF NOT EXISTS admins (
        user_id INTEGER PRIMARY KEY, username TEXT, role TEXT, added_date TEXT)''')
    c.execute('''CREATE TABLE IF NOT EXISTS store_settings (
        key TEXT PRIMARY KEY, value TEXT)''')
    c.execute('''CREATE TABLE IF NOT EXISTS news_updates (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        title TEXT, content TEXT, created_at TEXT)''')
    c.execute('''CREATE TABLE IF NOT EXISTS backup_history (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        backup_filename TEXT, created_at TEXT)''')

    # Add owner as admin
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    c.execute("INSERT OR IGNORE INTO users (user_id, username, joined_date, last_active, is_admin) VALUES (?, ?, ?, ?, 1)",
              (OWNER_ID, "owner", now, now))
    c.execute("INSERT OR IGNORE INTO admins (user_id, username, role, added_date) VALUES (?, ?, 'owner', ?)",
              (OWNER_ID, "owner", now))
    for aid in ADMIN_IDS:
        c.execute("INSERT OR IGNORE INTO admins (user_id, username, role, added_date) VALUES (?, ?, 'admin', ?)",
                  (aid, f"admin_{aid}", now))
        c.execute("UPDATE users SET is_admin = 1 WHERE user_id = ?", (aid,))

    # Default store settings
    c.execute("INSERT OR IGNORE INTO store_settings (key, value) VALUES ('store_name', ?)", (SHOP_NAME,))
    conn.commit()
    conn.close()
    print("✅ Database initialized (no sample products).")

def is_admin(user_id):
    return user_id == OWNER_ID or user_id in ADMIN_IDS

def get_all_admin_ids():
    return [OWNER_ID] + ADMIN_IDS

def get_cart(user_id):
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("SELECT id, product_id, product_name, product_price, quantity FROM cart WHERE user_id=?", (user_id,))
    items = c.fetchall()
    conn.close()
    return items

def get_cart_total(user_id):
    items = get_cart(user_id)
    return sum(i[3] * i[4] for i in items)

def clear_cart(user_id):
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("DELETE FROM cart WHERE user_id=?", (user_id,))
    conn.commit()
    conn.close()

def add_to_cart(user_id, product_id, qty):
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("SELECT name, price, stock FROM products WHERE id=? AND is_active=1", (product_id,))
    prod = c.fetchone()
    if not prod:
        conn.close()
        return False, "Product not found"
    name, price, stock = prod
    if stock == 0:
        conn.close()
        return False, "Out of stock"
    if stock > 0 and stock < qty:
        conn.close()
        return False, f"Only {stock} left"
    c.execute("SELECT id, quantity FROM cart WHERE user_id=? AND product_id=?", (user_id, product_id))
    existing = c.fetchone()
    if existing:
        new_qty = existing[1] + qty
        c.execute("UPDATE cart SET quantity=? WHERE id=?", (new_qty, existing[0]))
    else:
        c.execute("INSERT INTO cart (user_id, product_id, product_name, product_price, quantity) VALUES (?,?,?,?,?)",
                  (user_id, product_id, name, price, qty))
    conn.commit()
    conn.close()
    return True, "Added"

def create_order(user_id, items, phone, customer_name):
    order_number = f"ORD{datetime.now().strftime('%Y%m%d%H%M%S')}{random.randint(100,999)}"
    total = sum(i[3]*i[4] for i in items)
    product_names = ", ".join([i[2] for i in items[:3]]) + ("..." if len(items)>3 else "")
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    notes = json.dumps([{"product_id": i[1], "name": i[2], "price": i[3], "qty": i[4]} for i in items])
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute('''INSERT INTO orders (order_number, user_id, product_name, total_amount,
                customer_phone, customer_name, payment_status, order_status, notes, created_at)
                VALUES (?,?,?,?,?,?,?,?,?,?)''',
              (order_number, user_id, product_names, total, phone, customer_name,
               'pending', 'pending', notes, now))
    order_id = c.lastrowid
    # reduce stock
    for item in items:
        pid = item[1]
        qty = item[4]
        c.execute("SELECT stock FROM products WHERE id=?", (pid,))
        stock = c.fetchone()[0]
        if stock > 0:
            c.execute("UPDATE products SET stock = stock - ? WHERE id=?", (qty, pid))
    c.execute("DELETE FROM cart WHERE user_id=?", (user_id,))
    conn.commit()
    conn.close()
    return {"id": order_id, "order_number": order_number, "total_amount": total}

def get_all_categories():
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("SELECT name, emoji FROM categories ORDER BY sort_order")
    cats = c.fetchall()
    conn.close()
    return cats

def get_products_by_category(category):
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("SELECT id, name, price, stock FROM products WHERE category=? AND is_active=1 ORDER BY name", (category,))
    prods = c.fetchall()
    conn.close()
    return prods

def get_product(pid):
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("SELECT id, name, category, price, description, image_file_id, stock, avg_rating, total_reviews FROM products WHERE id=? AND is_active=1", (pid,))
    prod = c.fetchone()
    conn.close()
    return prod

def add_product(name, category, price, desc, image_id, stock):
    uid = str(uuid.uuid4())[:8]
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute('''INSERT INTO products (unique_id, name, category, price, description, image_file_id, stock, created_at)
                 VALUES (?,?,?,?,?,?,?,?)''', (uid, name, category, price, desc, image_id, stock, now))
    conn.commit()
    conn.close()

def update_product_field(pid, field, value):
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute(f"UPDATE products SET {field}=? WHERE id=?", (value, pid))
    conn.commit()
    conn.close()

def delete_product(pid):
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("DELETE FROM products WHERE id=?", (pid,))
    conn.commit()
    conn.close()

def add_category(name, emoji):
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("SELECT MAX(sort_order) FROM categories")
    max_order = c.fetchone()[0] or 0
    c.execute("INSERT INTO categories (name, emoji, sort_order) VALUES (?,?,?)", (name, emoji, max_order+1))
    conn.commit()
    conn.close()

def delete_category(cat_name):
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("DELETE FROM categories WHERE name=?", (cat_name,))
    c.execute("UPDATE products SET category='Uncategorized' WHERE category=?", (cat_name,))
    conn.commit()
    conn.close()

def get_all_products_admin():
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("SELECT id, name, price, stock, is_active FROM products ORDER BY name")
    prods = c.fetchall()
    conn.close()
    return prods

def get_pending_orders_count():
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("SELECT COUNT(*) FROM orders WHERE payment_status='paid' AND order_status NOT IN ('delivered','cancelled')")
    cnt = c.fetchone()[0]
    conn.close()
    return cnt

def get_orders_awaiting_receipt():
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("SELECT id, order_number, product_name, total_amount, customer_name FROM orders WHERE order_status='awaiting_receipt'")
    orders = c.fetchall()
    conn.close()
    return orders

def mark_order_paid(order_id):
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("UPDATE orders SET payment_status='paid', order_status='awaiting_receipt' WHERE id=?", (order_id,))
    c.execute("SELECT user_id, total_amount, order_number FROM orders WHERE id=?", (order_id,))
    order = c.fetchone()
    if order:
        user_id, amount, order_num = order
        c.execute("UPDATE users SET total_orders=total_orders+1, total_spent=total_spent+? WHERE user_id=?", (amount, user_id))
    conn.commit()
    conn.close()
    if order:
        bot.send_message(user_id, f"✅ Payment received for order #{order_num}!\nPlease upload your payment receipt.")
        pending_receipts[user_id] = order_id

def verify_receipt(order_id):
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("UPDATE orders SET order_status='processing' WHERE id=?", (order_id,))
    c.execute("SELECT user_id, order_number FROM orders WHERE id=?", (order_id,))
    user_id, order_num = c.fetchone()
    conn.commit()
    conn.close()
    bot.send_message(user_id, f"✅ Receipt verified! Order #{order_num} is now being processed.\nPlease share your delivery location.", reply_markup=location_markup())
    pending_locations[user_id] = order_id

def location_markup():
    mk = ReplyKeyboardMarkup(resize_keyboard=True)
    mk.add(KeyboardButton("📍 Share Location", request_location=True))
    mk.add(KeyboardButton("🔙 Back"))
    return mk

# ==================== KHQR (simplified fallback) ====================
class SimpleKHPay:
    def generate_qr(self, amount, note=""):
        # Manual fallback – just return bank details
        txn_id = f"MANUAL_{int(time.time())}_{random.randint(1000,9999)}"
        qr_data = (f"Bank: {MANUAL_PAYMENT_BANK_NAME}\nAccount: {MANUAL_PAYMENT_ACCOUNT_NUMBER}\n"
                   f"Name: {MANUAL_PAYMENT_ACCOUNT_NAME}\nAmount: ${amount:.2f}\nRef: {note}")
        return {"transaction_id": txn_id, "qr_string": qr_data, "is_fallback": True}
khpay = SimpleKHPay()

# ==================== MAIN MENU ====================
def main_menu(user_id):
    mk = ReplyKeyboardMarkup(resize_keyboard=True, row_width=2)
    btns = ["🛒 SHOP NOW", "🛒 CART", "📦 MY ORDERS", "🚚 TRACK ORDER", "👤 PROFILE", "📞 CONTACT", "🌍 LANGUAGE"]
    if is_admin(user_id):
        btns.append("🔐 ADMIN")
    mk.add(*[KeyboardButton(b) for b in btns])
    return mk

@bot.message_handler(commands=['start'])
def start(msg):
    user_id = msg.from_user.id
    save_user(msg)
    bot.send_message(msg.chat.id, f"Welcome {msg.from_user.first_name}!\nUse the buttons below to shop.", reply_markup=main_menu(user_id))

def save_user(msg, phone=None):
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    c.execute("SELECT user_id FROM users WHERE user_id=?", (msg.from_user.id,))
    if not c.fetchone():
        c.execute("INSERT INTO users (user_id, username, first_name, joined_date, last_active) VALUES (?,?,?,?,?)",
                  (msg.from_user.id, msg.from_user.username, msg.from_user.first_name, now, now))
    else:
        c.execute("UPDATE users SET last_active=? WHERE user_id=?", (now, msg.from_user.id))
    if phone:
        c.execute("UPDATE users SET phone=? WHERE user_id=?", (phone, msg.from_user.id))
    conn.commit()
    conn.close()

# ==================== SHOP NOW ====================
@bot.message_handler(func=lambda m: m.text == "🛒 SHOP NOW")
def shop_now(msg):
    cats = get_all_categories()
    if not cats:
        bot.send_message(msg.chat.id, "No categories yet. Admin can add them.")
        return
    mk = InlineKeyboardMarkup(row_width=2)
    for name, emoji in cats:
        mk.add(InlineKeyboardButton(f"{emoji} {name}", callback_data=f"cat_{name}"))
    bot.send_message(msg.chat.id, "Select category:", reply_markup=mk)

@bot.callback_query_handler(func=lambda call: call.data.startswith("cat_"))
def show_products(call):
    cat = call.data[4:]
    prods = get_products_by_category(cat)
    if not prods:
        bot.answer_callback_query(call.id, "No products in this category")
        return
    mk = InlineKeyboardMarkup(row_width=1)
    for pid, name, price, stock in prods:
        stock_str = " ⚠️ low" if 0 < stock < 5 else (" ✅" if stock > 0 else " ❌")
        mk.add(InlineKeyboardButton(f"{name} — ${price:.2f}{stock_str}", callback_data=f"view_{pid}"))
    mk.add(InlineKeyboardButton("🔙 Back", callback_data="back_cats"))
    bot.edit_message_text(f"📦 {cat}", call.message.chat.id, call.message.message_id, reply_markup=mk)

@bot.callback_query_handler(func=lambda call: call.data == "back_cats")
def back_cats(call):
    cats = get_all_categories()
    mk = InlineKeyboardMarkup(row_width=2)
    for name, emoji in cats:
        mk.add(InlineKeyboardButton(f"{emoji} {name}", callback_data=f"cat_{name}"))
    bot.edit_message_text("Select category:", call.message.chat.id, call.message.message_id, reply_markup=mk)

@bot.callback_query_handler(func=lambda call: call.data.startswith("view_"))
def view_product(call):
    pid = int(call.data.split("_")[1])
    prod = get_product(pid)
    if not prod:
        bot.answer_callback_query(call.id, "Product not found")
        return
    pid, name, cat, price, desc, img, stock, rating, revs = prod
    txt = f"📦 <b>{name}</b>\n💰 ${price:.2f}\n📂 {cat}\n📝 {desc or 'No description'}\n📊 Stock: {'Unlimited' if stock==-1 else stock}"
    if rating:
        txt += f"\n⭐ Rating: {rating}/5 ({revs} reviews)"
    mk = InlineKeyboardMarkup(row_width=2)
    if stock != 0:
        mk.add(InlineKeyboardButton("🛒 Add to Cart", callback_data=f"add_{pid}"),
               InlineKeyboardButton("💳 Buy Now", callback_data=f"buy_{pid}"))
    else:
        mk.add(InlineKeyboardButton("🔔 Notify me", callback_data=f"notify_{pid}"))
    mk.add(InlineKeyboardButton("⭐ Reviews", callback_data=f"reviews_{pid}"),
           InlineKeyboardButton("🔙 Back", callback_data="back_cats"))
    if img:
        bot.send_photo(call.message.chat.id, img, caption=txt, reply_markup=mk)
    else:
        bot.send_message(call.message.chat.id, txt, reply_markup=mk)
    bot.answer_callback_query(call.id)

# ==================== ADD TO CART ====================
@bot.callback_query_handler(func=lambda call: call.data.startswith("add_"))
def add_to_cart_cb(call):
    pid = int(call.data.split("_")[1])
    user_id = call.from_user.id
    ok, msg = add_to_cart(user_id, pid, 1)
    bot.answer_callback_query(call.id, msg)
    if ok:
        cart_count = len(get_cart(user_id))
        bot.send_message(call.message.chat.id, f"Added to cart! Cart has {cart_count} item(s).", reply_markup=main_menu(user_id))

@bot.callback_query_handler(func=lambda call: call.data.startswith("buy_"))
def buy_now(call):
    pid = int(call.data.split("_")[1])
    user_id = call.from_user.id
    prod = get_product(pid)
    if not prod or prod[6] == 0:
        bot.answer_callback_query(call.id, "Out of stock")
        return
    user_states[user_id] = {"action": "buy", "product_id": pid, "qty": 1}
    ask_phone(call.message.chat.id, user_id)

def ask_phone(chat_id, user_id):
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("SELECT phone FROM users WHERE user_id=?", (user_id,))
    saved = c.fetchone()
    conn.close()
    if saved and saved[0]:
        mk = InlineKeyboardMarkup()
        mk.add(InlineKeyboardButton("✅ Use saved", callback_data="use_saved_phone"),
               InlineKeyboardButton("📝 Enter new", callback_data="new_phone"))
        bot.send_message(chat_id, f"Use saved phone: {saved[0]}?", reply_markup=mk)
    else:
        msg = bot.send_message(chat_id, "📞 Enter your phone number:")
        bot.register_next_step_handler(msg, process_phone)

@bot.callback_query_handler(func=lambda call: call.data in ["use_saved_phone", "new_phone"])
def phone_callback(call):
    user_id = call.from_user.id
    if call.data == "use_saved_phone":
        conn = sqlite3.connect(DB_PATH)
        c = conn.cursor()
        c.execute("SELECT phone FROM users WHERE user_id=?", (user_id,))
        phone = c.fetchone()[0]
        conn.close()
        if phone:
            user_states[user_id]["phone"] = phone
            proceed_payment(call.message.chat.id, user_id)
        else:
            bot.answer_callback_query(call.id, "No saved phone")
            msg = bot.send_message(call.message.chat.id, "Enter phone:")
            bot.register_next_step_handler(msg, process_phone)
    else:
        msg = bot.send_message(call.message.chat.id, "📞 Enter phone number:")
        bot.register_next_step_handler(msg, process_phone)
    bot.answer_callback_query(call.id)

def process_phone(msg):
    user_id = msg.from_user.id
    phone = msg.text.strip()
    if not re.match(r'^[\+\d\s\-]{8,}$', phone):
        bot.send_message(msg.chat.id, "Invalid phone, try again:")
        bot.register_next_step_handler(msg, process_phone)
        return
    save_user(msg, phone)
    user_states[user_id]["phone"] = phone
    proceed_payment(msg.chat.id, user_id)

def proceed_payment(chat_id, user_id):
    state = user_states.get(user_id)
    if not state:
        bot.send_message(chat_id, "Session expired")
        return
    if state["action"] == "buy":
        pid = state["product_id"]
        prod = get_product(pid)
        if not prod or prod[6] == 0:
            bot.send_message(chat_id, "Product out of stock")
            return
        name, price = prod[1], prod[4]
        total = price
        order = create_order(user_id, [(0, pid, name, price, 1)], state["phone"], bot.get_chat(user_id).first_name)
    elif state["action"] == "cart":
        items = get_cart(user_id)
        if not items:
            bot.send_message(chat_id, "Cart empty")
            return
        order = create_order(user_id, items, state["phone"], bot.get_chat(user_id).first_name)
    else:
        return
    if not order:
        bot.send_message(chat_id, "Order failed")
        return
    # Generate QR / manual payment
    qr_data = khpay.generate_qr(order["total_amount"], note=order["order_number"])
    qr_img = qrcode.make(qr_data["qr_string"])
    bio = BytesIO()
    qr_img.save(bio, "PNG")
    bio.seek(0)
    pay_text = f"Order #{order['order_number']}\nAmount: ${order['total_amount']:.2f}\n\n"
    if qr_data.get("is_fallback"):
        pay_text += f"Manual transfer to:\n🏦 {MANUAL_PAYMENT_BANK_NAME}\n📱 {MANUAL_PAYMENT_ACCOUNT_NUMBER}\n👤 {MANUAL_PAYMENT_ACCOUNT_NAME}\n\nAfter payment, click UPLOAD RECEIPT."
    else:
        pay_text += "Scan QR code to pay."
    mk = InlineKeyboardMarkup()
    mk.add(InlineKeyboardButton("📸 Upload Receipt", callback_data=f"upload_{order['id']}"))
    bot.send_photo(chat_id, bio, caption=pay_text, reply_markup=mk)
    active_payments[order["id"]] = {"user_id": user_id, "order_id": order["id"]}
    user_states.pop(user_id, None)

@bot.callback_query_handler(func=lambda call: call.data.startswith("upload_"))
def upload_receipt(call):
    order_id = int(call.data.split("_")[1])
    pending_receipts[call.from_user.id] = order_id
    bot.send_message(call.message.chat.id, "📸 Send the payment receipt photo.")
    bot.answer_callback_query(call.id)

@bot.message_handler(content_types=['photo'])
def handle_receipt_photo(msg):
    user_id = msg.from_user.id
    if user_id in pending_receipts:
        order_id = pending_receipts[user_id]
        # store receipt image id in order
        conn = sqlite3.connect(DB_PATH)
        c = conn.cursor()
        c.execute("UPDATE orders SET receipt_image_id=? WHERE id=?", (msg.photo[-1].file_id, order_id))
        conn.commit()
        conn.close()
        bot.send_message(user_id, "Receipt saved. Admin will verify soon.")
        for admin in get_all_admin_ids():
            bot.send_message(admin, f"New receipt from user {user_id} for order #{order_id}\nUse /admin to verify.")
        del pending_receipts[user_id]

# ==================== CART ====================
@bot.message_handler(func=lambda m: m.text == "🛒 CART")
def show_cart(msg):
    user_id = msg.from_user.id
    items = get_cart(user_id)
    if not items:
        bot.send_message(msg.chat.id, "Cart empty", reply_markup=main_menu(user_id))
        return
    total = get_cart_total(user_id)
    txt = "🛒 YOUR CART\n"
    for it in items:
        txt += f"• {it[2]} x{it[4]} = ${it[3]*it[4]:.2f}\n"
    txt += f"Total: ${total:.2f}"
    mk = InlineKeyboardMarkup()
    mk.add(InlineKeyboardButton("✅ Checkout", callback_data="checkout_cart"),
           InlineKeyboardButton("🗑️ Clear", callback_data="clear_cart"))
    bot.send_message(msg.chat.id, txt, reply_markup=mk)

@bot.callback_query_handler(func=lambda call: call.data == "checkout_cart")
def checkout_cart(call):
    user_id = call.from_user.id
    items = get_cart(user_id)
    if not items:
        bot.answer_callback_query(call.id, "Cart empty")
        return
    user_states[user_id] = {"action": "cart"}
    ask_phone(call.message.chat.id, user_id)
    bot.answer_callback_query(call.id)

@bot.callback_query_handler(func=lambda call: call.data == "clear_cart")
def clear_cart_cb(call):
    clear_cart(call.from_user.id)
    bot.answer_callback_query(call.id, "Cart cleared")
    bot.send_message(call.message.chat.id, "Cart cleared", reply_markup=main_menu(call.from_user.id))

# ==================== MY ORDERS ====================
@bot.message_handler(func=lambda m: m.text == "📦 MY ORDERS")
def my_orders(msg):
    user_id = msg.from_user.id
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("SELECT order_number, product_name, total_amount, order_status, created_at FROM orders WHERE user_id=? ORDER BY id DESC LIMIT 10", (user_id,))
    orders = c.fetchall()
    conn.close()
    if not orders:
        bot.send_message(msg.chat.id, "No orders", reply_markup=main_menu(user_id))
        return
    txt = "📦 Recent orders:\n"
    for o in orders:
        txt += f"#{o[0]} - {o[1][:20]} - ${o[2]:.2f} - {ORDER_STATUSES.get(o[3], o[3])} - {o[4][:10]}\n"
    bot.send_message(msg.chat.id, txt, reply_markup=main_menu(user_id))

# ==================== TRACK ORDER ====================
@bot.message_handler(func=lambda m: m.text == "🚚 TRACK ORDER")
def track_order_start(msg):
    sent = bot.send_message(msg.chat.id, "Enter order number:")
    bot.register_next_step_handler(sent, track_order_number)

def track_order_number(msg):
    order_num = msg.text.strip().upper()
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("SELECT order_number, product_name, total_amount, order_status, created_at, user_id FROM orders WHERE order_number=?", (order_num,))
    order = c.fetchone()
    conn.close()
    if not order or (order[5] != msg.from_user.id and not is_admin(msg.from_user.id)):
        bot.send_message(msg.chat.id, "Order not found or not yours")
        return
    txt = f"Order #{order[0]}\nProduct: {order[1]}\nAmount: ${order[2]:.2f}\nStatus: {ORDER_STATUSES.get(order[3], order[3])}\nDate: {order[4][:16]}"
    bot.send_message(msg.chat.id, txt, reply_markup=main_menu(msg.from_user.id))

# ==================== PROFILE ====================
@bot.message_handler(func=lambda m: m.text == "👤 PROFILE")
def profile(msg):
    user_id = msg.from_user.id
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("SELECT phone, total_orders, total_spent FROM users WHERE user_id=?", (user_id,))
    data = c.fetchone()
    conn.close()
    phone = data[0] if data else "Not set"
    orders = data[1] if data else 0
    spent = data[2] if data else 0
    txt = f"👤 Profile\nPhone: {phone}\nOrders: {orders}\nSpent: ${spent:.2f}"
    bot.send_message(msg.chat.id, txt, reply_markup=main_menu(user_id))

# ==================== CONTACT ====================
@bot.message_handler(func=lambda m: m.text == "📞 CONTACT")
def contact(msg):
    txt = f"📞 Contact:\nPhone: {CONTACT_PHONE}\nTelegram: {CONTACT_TELEGRAM}"
    bot.send_message(msg.chat.id, txt, reply_markup=main_menu(msg.from_user.id))

# ==================== LANGUAGE (simplified) ====================
@bot.message_handler(func=lambda m: m.text == "🌍 LANGUAGE")
def language_menu(msg):
    mk = InlineKeyboardMarkup(row_width=2)
    mk.add(InlineKeyboardButton("🇬🇧 English", callback_data="lang_en"),
           InlineKeyboardButton("🇰🇭 Khmer", callback_data="lang_km"),
           InlineKeyboardButton("🇨🇳 中文", callback_data="lang_zh"))
    bot.send_message(msg.chat.id, "Select language:", reply_markup=mk)

@bot.callback_query_handler(func=lambda call: call.data.startswith("lang_"))
def set_lang(call):
    lang = call.data[5:]
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("UPDATE users SET language=? WHERE user_id=?", (lang, call.from_user.id))
    conn.commit()
    conn.close()
    bot.answer_callback_query(call.id, f"Language set to {lang}")
    start(call.message)

# ==================== ADMIN PANEL ====================
@bot.message_handler(func=lambda m: m.text == "🔐 ADMIN" and is_admin(m.from_user.id))
def admin_panel(msg):
    pending = get_pending_orders_count()
    awaiting = len(get_orders_awaiting_receipt())
    txt = "🔐 Admin panel\n"
    if pending: txt += f"🚚 {pending} pending orders\n"
    if awaiting: txt += f"📸 {awaiting} receipts to verify\n"
    mk = ReplyKeyboardMarkup(resize_keyboard=True, row_width=2)
    btns = ["➕ Add Product", "📦 Manage Products", "📁 Add Category", "🗑️ Remove Category",
            "📢 Broadcast", "📸 Verify Receipts", "📊 Stats", "👥 Users", "🧾 Receipt", "🔙 Back"]
    mk.add(*[KeyboardButton(b) for b in btns])
    bot.send_message(msg.chat.id, txt, reply_markup=mk)

# Add product flow
@bot.message_handler(func=lambda m: m.text == "➕ Add Product" and is_admin(m.from_user.id))
def add_prod_start(msg):
    user_states[msg.from_user.id] = {"action": "add_prod"}
    bot.send_message(msg.chat.id, "Product name:")
    bot.register_next_step_handler(msg, add_prod_name)

def add_prod_name(msg):
    user_states[msg.from_user.id]["name"] = msg.text
    bot.send_message(msg.chat.id, "Category (existing):")
    bot.register_next_step_handler(msg, add_prod_cat)

def add_prod_cat(msg):
    user_states[msg.from_user.id]["cat"] = msg.text
    bot.send_message(msg.chat.id, "Price (USD):")
    bot.register_next_step_handler(msg, add_prod_price)

def add_prod_price(msg):
    try:
        price = float(msg.text)
        user_states[msg.from_user.id]["price"] = price
        bot.send_message(msg.chat.id, "Description:")
        bot.register_next_step_handler(msg, add_prod_desc)
    except:
        bot.reply_to(msg, "Invalid price, try again")
        bot.register_next_step_handler(msg, add_prod_price)

def add_prod_desc(msg):
    user_states[msg.from_user.id]["desc"] = msg.text
    bot.send_message(msg.chat.id, "Stock (-1 = unlimited):")
    bot.register_next_step_handler(msg, add_prod_stock)

def add_prod_stock(msg):
    try:
        stock = int(msg.text)
        user_states[msg.from_user.id]["stock"] = stock
        bot.send_message(msg.chat.id, "Send product image (or /skip):")
        bot.register_next_step_handler(msg, add_prod_image)
    except:
        bot.reply_to(msg, "Invalid number")
        bot.register_next_step_handler(msg, add_prod_stock)

def add_prod_image(msg):
    img = None
    if msg.text == "/skip":
        img = None
    elif msg.photo:
        img = msg.photo[-1].file_id
    else:
        bot.reply_to(msg, "Send photo or /skip")
        bot.register_next_step_handler(msg, add_prod_image)
        return
    data = user_states[msg.from_user.id]
    add_product(data["name"], data["cat"], data["price"], data["desc"], img, data["stock"])
    bot.send_message(msg.chat.id, "✅ Product added!", reply_markup=admin_panel_buttons(msg.from_user.id))
    user_states.pop(msg.from_user.id, None)

# Manage products (list, edit, delete)
@bot.message_handler(func=lambda m: m.text == "📦 Manage Products" and is_admin(m.from_user.id))
def manage_products(msg):
    prods = get_all_products_admin()
    if not prods:
        bot.send_message(msg.chat.id, "No products")
        return
    mk = InlineKeyboardMarkup(row_width=1)
    for pid, name, price, stock, active in prods:
        status = "✅" if active else "❌"
        mk.add(InlineKeyboardButton(f"{status} {name} - ${price:.2f} (stock:{stock})", callback_data=f"edit_{pid}"))
    bot.send_message(msg.chat.id, "Select product to edit:", reply_markup=mk)

@bot.callback_query_handler(func=lambda call: call.data.startswith("edit_") and is_admin(call.from_user.id))
def edit_product_menu(call):
    pid = int(call.data.split("_")[1])
    user_states[call.from_user.id] = {"action": "edit", "pid": pid}
    mk = InlineKeyboardMarkup(row_width=2)
    mk.add(InlineKeyboardButton("💰 Price", callback_data=f"editf_price_{pid}"),
           InlineKeyboardButton("📦 Stock", callback_data=f"editf_stock_{pid}"),
           InlineKeyboardButton("📝 Name", callback_data=f"editf_name_{pid}"),
           InlineKeyboardButton("🖼️ Image", callback_data=f"editf_image_{pid}"),
           InlineKeyboardButton("✅ Toggle Active", callback_data=f"editf_active_{pid}"),
           InlineKeyboardButton("🗑️ Delete", callback_data=f"editf_delete_{pid}"),
           InlineKeyboardButton("🔙 Back", callback_data="back_admin_prods"))
    bot.send_message(call.message.chat.id, "Edit options:", reply_markup=mk)

@bot.callback_query_handler(func=lambda call: call.data.startswith("editf_") and is_admin(call.from_user.id))
def edit_field(call):
    _, field, pid = call.data.split("_")
    pid = int(pid)
    if field == "price":
        msg = bot.send_message(call.message.chat.id, "New price:")
        bot.register_next_step_handler(msg, lambda m: update_field(m, pid, "price", float))
    elif field == "stock":
        msg = bot.send_message(call.message.chat.id, "New stock (-1=unlimited):")
        bot.register_next_step_handler(msg, lambda m: update_field(m, pid, "stock", int))
    elif field == "name":
        msg = bot.send_message(call.message.chat.id, "New name:")
        bot.register_next_step_handler(msg, lambda m: update_field(m, pid, "name", str))
    elif field == "image":
        msg = bot.send_message(call.message.chat.id, "Send new image:")
        bot.register_next_step_handler(msg, update_image, pid)
    elif field == "active":
        conn = sqlite3.connect(DB_PATH)
        c = conn.cursor()
        c.execute("SELECT is_active FROM products WHERE id=?", (pid,))
        cur = c.fetchone()[0]
        new = 0 if cur else 1
        c.execute("UPDATE products SET is_active=? WHERE id=?", (new, pid))
        conn.commit()
        conn.close()
        bot.answer_callback_query(call.id, f"Product {'activated' if new else 'deactivated'}")
        manage_products(call.message)
    elif field == "delete":
        conn = sqlite3.connect(DB_PATH)
        c = conn.cursor()
        c.execute("DELETE FROM products WHERE id=?", (pid,))
        conn.commit()
        conn.close()
        bot.answer_callback_query(call.id, "Deleted")
        manage_products(call.message)

def update_field(msg, pid, field, converter):
    try:
        val = converter(msg.text)
        conn = sqlite3.connect(DB_PATH)
        c = conn.cursor()
        c.execute(f"UPDATE products SET {field}=? WHERE id=?", (val, pid))
        conn.commit()
        conn.close()
        bot.send_message(msg.chat.id, f"✅ {field} updated")
    except:
        bot.send_message(msg.chat.id, "Invalid value")
    manage_products(msg)

def update_image(msg, pid):
    if msg.photo:
        img = msg.photo[-1].file_id
        conn = sqlite3.connect(DB_PATH)
        c = conn.cursor()
        c.execute("UPDATE products SET image_file_id=? WHERE id=?", (img, pid))
        conn.commit()
        conn.close()
        bot.send_message(msg.chat.id, "Image updated")
    else:
        bot.send_message(msg.chat.id, "Not a photo")
    manage_products(msg)

@bot.callback_query_handler(func=lambda call: call.data == "back_admin_prods" and is_admin(call.from_user.id))
def back_admin_prods(call):
    manage_products(call.message)

# Categories
@bot.message_handler(func=lambda m: m.text == "📁 Add Category" and is_admin(m.from_user.id))
def add_cat_start(msg):
    bot.send_message(msg.chat.id, "Category name:")
    bot.register_next_step_handler(msg, add_cat_name)

def add_cat_name(msg):
    name = msg.text.strip()
    bot.send_message(msg.chat.id, "Emoji (e.g., 👕):")
    bot.register_next_step_handler(msg, lambda m: add_cat_emoji(m, name))

def add_cat_emoji(msg, name):
    emoji = msg.text.strip() or "📦"
    add_category(name, emoji)
    bot.send_message(msg.chat.id, f"Category {emoji} {name} added", reply_markup=admin_panel_buttons(msg.from_user.id))

@bot.message_handler(func=lambda m: m.text == "🗑️ Remove Category" and is_admin(m.from_user.id))
def remove_cat_list(msg):
    cats = get_all_categories()
    if not cats:
        bot.send_message(msg.chat.id, "No categories")
        return
    mk = InlineKeyboardMarkup(row_width=1)
    for name, emoji in cats:
        mk.add(InlineKeyboardButton(f"{emoji} {name}", callback_data=f"delcat_{name}"))
    bot.send_message(msg.chat.id, "Select category to delete:", reply_markup=mk)

@bot.callback_query_handler(func=lambda call: call.data.startswith("delcat_") and is_admin(call.from_user.id))
def delcat_confirm(call):
    cat = call.data[7:]
    delete_category(cat)
    bot.answer_callback_query(call.id, f"Deleted {cat}")
    bot.send_message(call.message.chat.id, f"Category {cat} removed", reply_markup=admin_panel_buttons(call.from_user.id))

# Broadcast
@bot.message_handler(func=lambda m: m.text == "📢 Broadcast" and is_admin(m.from_user.id))
def broadcast_start(msg):
    bot.send_message(msg.chat.id, "Enter message to broadcast:")
    bot.register_next_step_handler(msg, send_broadcast)

def send_broadcast(msg):
    text = msg.text
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("SELECT user_id FROM users")
    users = c.fetchall()
    conn.close()
    sent = 0
    for u in users:
        try:
            bot.send_message(u[0], f"📢 BROADCAST\n\n{text}")
            sent += 1
            time.sleep(0.05)
        except:
            pass
    bot.send_message(msg.chat.id, f"Broadcast sent to {sent} users", reply_markup=admin_panel_buttons(msg.from_user.id))

# Verify receipts
@bot.message_handler(func=lambda m: m.text == "📸 Verify Receipts" and is_admin(m.from_user.id))
def verify_list(msg):
    orders = get_orders_awaiting_receipt()
    if not orders:
        bot.send_message(msg.chat.id, "No receipts pending")
        return
    mk = InlineKeyboardMarkup(row_width=1)
    for o in orders:
        oid, num, pname, total, cust = o
        mk.add(InlineKeyboardButton(f"{num} - {cust} - ${total:.2f}", callback_data=f"verify_{oid}"))
    bot.send_message(msg.chat.id, "Select order to verify receipt:", reply_markup=mk)

@bot.callback_query_handler(func=lambda call: call.data.startswith("verify_") and is_admin(call.from_user.id))
def show_receipt(call):
    oid = int(call.data.split("_")[1])
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("SELECT receipt_image_id, order_number, customer_name, total_amount FROM orders WHERE id=?", (oid,))
    img, num, cust, amt = c.fetchone()
    conn.close()
    if not img:
        bot.answer_callback_query(call.id, "No receipt image")
        return
    mk = InlineKeyboardMarkup()
    mk.add(InlineKeyboardButton("✅ Verify", callback_data=f"approve_{oid}"),
           InlineKeyboardButton("❌ Reject", callback_data=f"reject_{oid}"))
    bot.send_photo(call.message.chat.id, img, caption=f"Order {num}\n{cust} - ${amt:.2f}", reply_markup=mk)

@bot.callback_query_handler(func=lambda call: call.data.startswith("approve_") and is_admin(call.from_user.id))
def approve_receipt(call):
    oid = int(call.data.split("_")[1])
    verify_receipt(oid)
    bot.answer_callback_query(call.id, "Receipt verified, user will be asked for location")
    bot.send_message(call.message.chat.id, "Verified", reply_markup=admin_panel_buttons(call.from_user.id))

@bot.callback_query_handler(func=lambda call: call.data.startswith("reject_") and is_admin(call.from_user.id))
def reject_receipt(call):
    oid = int(call.data.split("_")[1])
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("SELECT user_id, order_number FROM orders WHERE id=?", (oid,))
    uid, num = c.fetchone()
    c.execute("UPDATE orders SET order_status='pending', payment_status='pending' WHERE id=?", (oid,))
    conn.commit()
    conn.close()
    bot.send_message(uid, f"❌ Your receipt for order {num} was rejected. Please upload again.")
    bot.answer_callback_query(call.id, "Rejected")
    bot.send_message(call.message.chat.id, "Rejected", reply_markup=admin_panel_buttons(call.from_user.id))

# Stats
@bot.message_handler(func=lambda m: m.text == "📊 Stats" and is_admin(m.from_user.id))
def stats(msg):
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("SELECT COUNT(*) FROM users")
    users = c.fetchone()[0]
    c.execute("SELECT COUNT(*), SUM(total_amount) FROM orders WHERE payment_status='paid'")
    orders, revenue = c.fetchone()
    revenue = revenue or 0
    c.execute("SELECT COUNT(*) FROM products WHERE is_active=1")
    prods = c.fetchone()[0]
    conn.close()
    txt = f"📊 Stats\nUsers: {users}\nOrders: {orders}\nRevenue: ${revenue:.2f}\nActive products: {prods}"
    bot.send_message(msg.chat.id, txt, reply_markup=admin_panel_buttons(msg.from_user.id))

# Users list
@bot.message_handler(func=lambda m: m.text == "👥 Users" and is_admin(m.from_user.id))
def list_users(msg):
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("SELECT user_id, username, first_name, phone, total_orders FROM users LIMIT 50")
    users = c.fetchall()
    conn.close()
    txt = "👥 Users:\n"
    for u in users:
        txt += f"• {u[2] or u[1] or u[0]} - {u[3] or 'no phone'} - {u[4]} orders\n"
    bot.send_message(msg.chat.id, txt, reply_markup=admin_panel_buttons(msg.from_user.id))

# Generate receipt
@bot.message_handler(func=lambda m: m.text == "🧾 Receipt" and is_admin(m.from_user.id))
def generate_receipt_admin(msg):
    bot.send_message(msg.chat.id, "Enter order number:")
    bot.register_next_step_handler(msg, gen_receipt_order)

def gen_receipt_order(msg):
    order_num = msg.text.strip().upper()
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("SELECT id, order_number, product_name, total_amount, customer_name, customer_phone, created_at FROM orders WHERE order_number=?", (order_num,))
    order = c.fetchone()
    conn.close()
    if not order:
        bot.send_message(msg.chat.id, "Order not found")
        return
    oid, num, pname, amt, cust, phone, date = order
    txt = f"🧾 RECEIPT\nOrder: {num}\nCustomer: {cust}\nPhone: {phone}\nProduct: {pname}\nAmount: ${amt:.2f}\nDate: {date[:16]}"
    if PDF_AVAILABLE:
        try:
            # Simple PDF generation
            buffer = BytesIO()
            doc = SimpleDocTemplate(buffer, pagesize=A4)
            story = []
            styles = getSampleStyleSheet()
            story.append(Paragraph(f"Receipt #{num}", styles['Title']))
            story.append(Spacer(1, 12))
            story.append(Paragraph(f"Customer: {cust}", styles['Normal']))
            story.append(Paragraph(f"Phone: {phone}", styles['Normal']))
            story.append(Paragraph(f"Product: {pname}", styles['Normal']))
            story.append(Paragraph(f"Amount: ${amt:.2f}", styles['Normal']))
            story.append(Paragraph(f"Date: {date}", styles['Normal']))
            doc.build(story)
            buffer.seek(0)
            bot.send_document(msg.chat.id, buffer, visible_file_name=f"receipt_{num}.pdf")
        except Exception as e:
            bot.send_message(msg.chat.id, f"PDF error: {e}\n\n{txt}")
    else:
        bot.send_message(msg.chat.id, txt)

# Back to main
@bot.message_handler(func=lambda m: m.text == "🔙 Back" and is_admin(m.from_user.id))
def back_from_admin(msg):
    start(msg)

def admin_panel_buttons(user_id):
    mk = ReplyKeyboardMarkup(resize_keyboard=True, row_width=2)
    btns = ["➕ Add Product", "📦 Manage Products", "📁 Add Category", "🗑️ Remove Category",
            "📢 Broadcast", "📸 Verify Receipts", "📊 Stats", "👥 Users", "🧾 Receipt", "🔙 Back"]
    mk.add(*[KeyboardButton(b) for b in btns])
    return mk

# Location handler
@bot.message_handler(content_types=['location'])
def location_handler(msg):
    user_id = msg.from_user.id
    if user_id in pending_locations:
        order_id = pending_locations[user_id]
        lat = msg.location.latitude
        lon = msg.location.longitude
        conn = sqlite3.connect(DB_PATH)
        c = conn.cursor()
        c.execute("UPDATE orders SET delivery_lat=?, delivery_lon=?, order_status='shipped' WHERE id=?", (lat, lon, order_id))
        conn.commit()
        conn.close()
        bot.send_message(user_id, "📍 Location saved. Your order is on the way!", reply_markup=main_menu(user_id))
        del pending_locations[user_id]

# Default fallback
@bot.message_handler(func=lambda m: True)
def fallback(msg):
    bot.send_message(msg.chat.id, "Use the buttons below.", reply_markup=main_menu(msg.from_user.id))

# ==================== RUN ====================
if __name__ == "__main__":
    init_db()
    print("Bot started. No sample products loaded – add them via admin panel.")
    bot.infinity_polling()
