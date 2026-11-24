"""
INTELLIGENT INVENTORY & PRIORITY MANAGEMENT SYSTEM - SPIDER-WEB EDITION
-----------------------------------------------------------------------
Run on Windows:
    py main.py

No third-party packages are required. Uses Tkinter and SQLite from Python.

Demo login:
    Username: admin
    Password: admin123

Your data is stored in your user profile (Windows: %APPDATA%/Spider), so it
is kept safe when the app is updated or reinstalled.

To make a normal Windows app (Spider.exe), double-click build_exe.bat.
"""

import csv
import hashlib
import heapq
import math
import os
import shutil
import sqlite3
import sys
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
from datetime import date, datetime, timedelta


APP_TITLE = "Spider - Intelligent Inventory & Priority Management"
DEMAND_WINDOW_DAYS = 30   # demand score is calculated from the last 30 days of sales


def resource_path(name):
    """Path to a bundled file (works both from source and from the built .exe)."""
    base = getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(__file__)))
    return os.path.join(base, name)


def app_data_dir():
    """Per-user folder for the database, created on first use."""
    if sys.platform.startswith("win"):
        base = os.environ.get("APPDATA") or os.path.expanduser("~")
    else:
        base = os.path.join(os.path.expanduser("~"), ".config")
    folder = os.path.join(base, "Spider")
    os.makedirs(folder, exist_ok=True)
    return folder


DB_FILE = os.path.join(app_data_dir(), "inventory.db")


def migrate_legacy_db():
    """Copy an old inventory_gui.db (next to the script/exe) into the user folder once."""
    here = os.path.dirname(sys.executable if getattr(sys, "frozen", False)
                           else os.path.abspath(__file__))
    older = os.path.join(os.path.dirname(app_data_dir()), "InventoryPro", "inventory.db")
    for legacy in (older, os.path.join(here, "inventory_gui.db")):
        if os.path.exists(legacy) and not os.path.exists(DB_FILE):
            shutil.copy2(legacy, DB_FILE)
ADMIN_USERNAME = "vicky"
ADMIN_PASSWORD_HASH = hashlib.sha256("vicky16".encode("utf-8")).hexdigest()

# Spider-Man palette: suit red, suit blue, web-shooter black/navy
BG = "#F4F5F9"
NAVY = "#0B1B3F"
BLUE = "#1E4FC2"
CYAN = "#3B82F6"
GREEN = "#12347A"
ORANGE = "#E62429"
RED = "#E62429"
DARK_RED = "#B3161B"
WHITE = "#FFFFFF"
TEXT = "#1F2A44"
MUTED = "#6B778C"
BANNER_BG = "#FDE9E7"
SEARCH_BG = "#F1F3F7"
SEARCH_HINT = "Search for products, categories and more"


def draw_web_logo(canvas, size, color=RED, body=NAVY):
    """Draw a spider-web logo (spokes + sagging rings + a tiny spider) on a canvas."""
    canvas.delete("all")
    cx = cy = size / 2
    radius = size * 0.46
    spokes = 8
    angles = [2 * math.pi * i / spokes - math.pi / 2 for i in range(spokes)]
    ring_width = max(1, round(size / 36))
    for a in angles:
        canvas.create_line(cx, cy, cx + radius * math.cos(a), cy + radius * math.sin(a),
                           fill=color, width=ring_width + 1, capstyle="round")
    for factor in (0.30, 0.52, 0.76, 1.0):
        r = radius * factor
        for i, a in enumerate(angles):
            b = angles[(i + 1) % spokes] if i + 1 < spokes else angles[0] + 2 * math.pi
            mid = (a + b) / 2
            sag = r * 0.84  # pull the middle inwards so strands sag like real silk
            canvas.create_line(
                cx + r * math.cos(a), cy + r * math.sin(a),
                cx + sag * math.cos(mid), cy + sag * math.sin(mid),
                cx + r * math.cos(b), cy + r * math.sin(b),
                smooth=True, fill=color, width=ring_width)
    body_r = size * 0.075
    canvas.create_oval(cx - body_r, cy - body_r * 1.25, cx + body_r, cy + body_r * 1.25,
                       fill=body, outline="")
    for k in (-1, 1):
        for dy in (-0.9, -0.3, 0.3, 0.9):
            canvas.create_line(cx + k * body_r * 0.8, cy + dy * body_r,
                               cx + k * body_r * 2.2, cy + dy * body_r * 1.8,
                               fill=body, width=max(1, ring_width - 1))


# ------------------------- DATA STRUCTURES -------------------------

class AVLNode:
    def __init__(self, key):
        self.key = key
        self.left = None
        self.right = None
        self.height = 1


class AVLTree:
    """AVL index for product IDs. The database remains the permanent storage."""
    def height(self, node):
        return node.height if node else 0

    def balance(self, node):
        return self.height(node.left) - self.height(node.right) if node else 0

    def rotate_right(self, y):
        x = y.left
        t2 = x.right
        x.right = y
        y.left = t2
        y.height = 1 + max(self.height(y.left), self.height(y.right))
        x.height = 1 + max(self.height(x.left), self.height(x.right))
        return x

    def rotate_left(self, x):
        y = x.right
        t2 = y.left
        y.left = x
        x.right = t2
        x.height = 1 + max(self.height(x.left), self.height(x.right))
        y.height = 1 + max(self.height(y.left), self.height(y.right))
        return y

    def insert(self, node, key):
        if node is None:
            return AVLNode(key)
        if key < node.key:
            node.left = self.insert(node.left, key)
        elif key > node.key:
            node.right = self.insert(node.right, key)
        else:
            return node

        node.height = 1 + max(self.height(node.left), self.height(node.right))
        b = self.balance(node)

        if b > 1 and key < node.left.key:
            return self.rotate_right(node)
        if b < -1 and key > node.right.key:
            return self.rotate_left(node)
        if b > 1 and key > node.left.key:
            node.left = self.rotate_left(node.left)
            return self.rotate_right(node)
        if b < -1 and key < node.right.key:
            node.right = self.rotate_right(node.right)
            return self.rotate_left(node)
        return node

    def contains(self, node, key):
        while node:
            if key == node.key:
                return True
            node = node.left if key < node.key else node.right
        return False


class TrieNode:
    def __init__(self):
        self.children = {}
        self.end = False


class ProductTrie:
    """Prefix search index for product names."""
    def __init__(self):
        self.root = TrieNode()
        self.names = []

    def build(self, names):
        self.root = TrieNode()
        self.names = list(names)
        for name in self.names:
            node = self.root
            for ch in name.lower():
                node = node.children.setdefault(ch, TrieNode())
            node.end = True

    def search_prefix(self, prefix):
        prefix = prefix.lower().strip()
        if not prefix:
            return self.names[:]
        node = self.root
        for ch in prefix:
            if ch not in node.children:
                return []
            node = node.children[ch]
        return [name for name in self.names if name.lower().startswith(prefix)]


# ------------------------- DATABASE -------------------------

class InventoryDB:
    def __init__(self, filename=DB_FILE):
        self.conn = sqlite3.connect(filename)
        self.conn.row_factory = sqlite3.Row
        self.conn.execute("PRAGMA foreign_keys = ON")
        self.create_tables()
        self.first_run_setup()

    def create_tables(self):
        with self.conn:
            self.conn.execute("""
                CREATE TABLE IF NOT EXISTS products (
                    product_id TEXT PRIMARY KEY,
                    barcode TEXT UNIQUE,
                    name TEXT NOT NULL,
                    category TEXT NOT NULL,
                    price REAL NOT NULL CHECK(price >= 0),
                    stock INTEGER NOT NULL CHECK(stock >= 0),
                    reorder_level INTEGER NOT NULL DEFAULT 5 CHECK(reorder_level >= 0),
                    demand INTEGER NOT NULL DEFAULT 1 CHECK(demand >= 0),
                    expiry TEXT,
                    updated_at TEXT NOT NULL
                )
            """)
            self.conn.execute("""
                CREATE TABLE IF NOT EXISTS sales (
                    sale_id INTEGER PRIMARY KEY AUTOINCREMENT,
                    product_id TEXT NOT NULL,
                    product_name TEXT NOT NULL,
                    quantity INTEGER NOT NULL,
                    unit_price REAL NOT NULL,
                    total REAL NOT NULL,
                    sale_date TEXT NOT NULL
                )
            """)
            self.conn.execute("""
                CREATE TABLE IF NOT EXISTS restocks (
                    restock_id INTEGER PRIMARY KEY AUTOINCREMENT,
                    product_id TEXT NOT NULL,
                    product_name TEXT NOT NULL,
                    quantity INTEGER NOT NULL CHECK(quantity > 0),
                    unit_cost REAL,
                    total_cost REAL NOT NULL DEFAULT 0,
                    supplier TEXT,
                    restock_date TEXT NOT NULL
                )
            """)
            self.conn.execute("""
                CREATE TABLE IF NOT EXISTS meta (
                    key TEXT PRIMARY KEY,
                    value TEXT
                )
            """)

    def first_run_setup(self):
        """Load demo data only on the very first run, so deleted items never come back."""
        done = self.conn.execute(
            "SELECT value FROM meta WHERE key='sample_loaded'").fetchone()
        if done is None:
            count = self.conn.execute("SELECT COUNT(*) FROM products").fetchone()[0]
            if count == 0:
                self.load_sample_data()
            with self.conn:
                self.conn.execute(
                    "INSERT OR REPLACE INTO meta (key, value) VALUES ('sample_loaded', '1')")

    def load_sample_data(self):
        """Add demo products, sales and restocks that are missing. Returns the counts added."""
        today = date.today()

        def exp(days):
            return (today + timedelta(days=days)).strftime("%Y-%m-%d")

        # (id, name, category, price, stock, reorder level, expiry)
        items = [
            ("P1001", "Wireless Mouse", "Electronics", 599, 24, 8, ""),
            ("P1002", "USB Keyboard", "Electronics", 899, 7, 10, ""),
            ("P1005", "LED Desk Lamp", "Electronics", 1299, 13, 5, ""),
            ("P1006", "Bluetooth Speaker", "Electronics", 1999, 4, 6, ""),
            ("P1007", "Power Bank 10000mAh", "Electronics", 1099, 18, 8, ""),
            ("P1008", "USB-C Cable", "Electronics", 299, 60, 20, ""),
            ("P1009", "Wireless Earbuds", "Electronics", 1499, 9, 10, ""),
            ("P1010", "HD Webcam", "Electronics", 1799, 3, 5, ""),
            ("P1003", "Notebook", "Stationery", 65, 45, 12, ""),
            ("P1011", "Gel Pen Pack", "Stationery", 120, 80, 25, ""),
            ("P1012", "A4 Paper Ream", "Stationery", 349, 14, 10, ""),
            ("P1013", "Stapler", "Stationery", 150, 6, 8, ""),
            ("P1014", "Highlighter Set", "Stationery", 180, 22, 10, ""),
            ("P1015", "Sticky Notes", "Stationery", 90, 35, 15, ""),
            ("P1004", "Water Bottle", "Home", 249, 5, 8, ""),
            ("P1016", "Steel Lunch Box", "Home", 549, 16, 8, ""),
            ("P1017", "Storage Basket", "Home", 399, 11, 6, ""),
            ("P1018", "Wall Clock", "Home", 699, 8, 5, ""),
            ("P1019", "Cotton Bedsheet", "Home", 1199, 12, 6, ""),
            ("P1020", "Basmati Rice 1kg", "Grocery", 140, 40, 15, exp(120)),
            ("P1021", "Almonds 250g", "Grocery", 320, 9, 10, exp(20)),
            ("P1022", "Green Tea Box", "Grocery", 210, 18, 8, exp(12)),
            ("P1023", "Peanut Butter", "Grocery", 275, 7, 8, exp(-5)),
            ("P1024", "Instant Noodles", "Grocery", 15, 120, 40, exp(45)),
            ("P1025", "Olive Oil 500ml", "Grocery", 540, 6, 6, exp(25)),
            ("P1026", "Hand Sanitizer", "Personal Care", 99, 30, 12, exp(200)),
            ("P1027", "Face Wash", "Personal Care", 245, 10, 10, exp(8)),
            ("P1028", "Shampoo", "Personal Care", 330, 15, 8, exp(90)),
            ("P1029", "Yoga Mat", "Sports", 799, 8, 5, ""),
            ("P1030", "Skipping Rope", "Sports", 199, 25, 8, ""),
        ]
        stamp = datetime.now().strftime("%Y-%m-%d %H:%M")
        products_added = 0
        with self.conn:
            for pid, name, cat, price, stock, reorder, expiry in items:
                cur = self.conn.execute("""
                    INSERT OR IGNORE INTO products
                    (product_id, barcode, name, category, price, stock,
                     reorder_level, demand, expiry, updated_at)
                    VALUES (?, ?, ?, ?, ?, ?, ?, 0, ?, ?)
                """, (pid, "890" + pid[1:], name, cat, price, stock, reorder,
                      expiry, stamp))
                products_added += cur.rowcount

        # Sample sales history: (product id, quantity, days ago, hour of day)
        sales = [
            ("P1008", 5, 0, 17), ("P1001", 2, 0, 15), ("P1024", 20, 0, 12),
            ("P1007", 3, 1, 18), ("P1011", 10, 1, 11), ("P1006", 2, 1, 16),
            ("P1009", 2, 2, 14), ("P1020", 6, 2, 10), ("P1002", 3, 2, 13),
            ("P1004", 4, 3, 19), ("P1015", 8, 3, 12), ("P1027", 5, 3, 17),
            ("P1021", 3, 4, 11), ("P1001", 4, 4, 15), ("P1026", 9, 4, 18),
            ("P1012", 3, 5, 10), ("P1019", 2, 5, 16), ("P1003", 12, 5, 12),
            ("P1010", 1, 6, 14), ("P1016", 3, 6, 11), ("P1028", 4, 6, 17),
            ("P1022", 5, 7, 13), ("P1029", 2, 7, 18), ("P1008", 8, 7, 12),
            ("P1005", 2, 8, 15), ("P1023", 3, 8, 10), ("P1030", 4, 9, 16),
            ("P1013", 2, 9, 11), ("P1014", 6, 10, 14), ("P1017", 3, 10, 12),
            ("P1018", 2, 11, 17), ("P1025", 2, 12, 13), ("P1007", 4, 12, 18),
            ("P1009", 3, 13, 15), ("P1024", 30, 13, 11), ("P1011", 12, 14, 10),
        ]
        # Sample restocks: (product id, quantity, days ago, supplier, unit cost)
        restocks = [
            ("P1020", 30, 2, "FreshFarm Foods", 95), ("P1009", 8, 4, "TechSource Distributors", 1050),
            ("P1002", 10, 3, "TechSource Distributors", 620), ("P1021", 15, 5, "FreshFarm Foods", 210),
            ("P1004", 12, 6, "HomeLine Traders", 160), ("P1024", 60, 7, "FreshFarm Foods", 9),
            ("P1011", 40, 8, "PaperWorld Supplies", 70), ("P1027", 10, 9, "CarePlus Supplies", 150),
        ]
        info = {pid: (name, price) for pid, name, _c, price, *_ in items}

        def when(days_ago, hour):
            day = datetime.combine(today - timedelta(days=days_ago), datetime.min.time())
            return day.replace(hour=hour, minute=20).strftime("%Y-%m-%d %H:%M:%S")

        sales_added = restocks_added = 0
        if self.conn.execute("SELECT COUNT(*) FROM sales").fetchone()[0] == 0:
            with self.conn:
                for pid, qty, days_ago, hour in sales:
                    name, price = info[pid]
                    self.conn.execute("""
                        INSERT INTO sales
                        (product_id, product_name, quantity, unit_price, total, sale_date)
                        VALUES (?, ?, ?, ?, ?, ?)
                    """, (pid, name, qty, price, price * qty, when(days_ago, hour)))
                    sales_added += 1
        if self.conn.execute("SELECT COUNT(*) FROM restocks").fetchone()[0] == 0:
            with self.conn:
                for pid, qty, days_ago, supplier, cost in restocks:
                    self.conn.execute("""
                        INSERT INTO restocks
                        (product_id, product_name, quantity, unit_cost, total_cost,
                         supplier, restock_date)
                        VALUES (?, ?, ?, ?, ?, ?, ?)
                    """, (pid, info[pid][0], qty, cost, cost * qty, supplier,
                          when(days_ago, 9)))
                    restocks_added += 1
        return products_added, sales_added, restocks_added

    def all_products(self):
        return self.conn.execute(
            "SELECT * FROM products ORDER BY name COLLATE NOCASE"
        ).fetchall()

    def get_product(self, product_id):
        return self.conn.execute(
            "SELECT * FROM products WHERE product_id = ?", (product_id,)
        ).fetchone()

    def save_product(self, data, editing=False):
        barcode = data["barcode"].strip() or None
        now = datetime.now().strftime("%Y-%m-%d %H:%M")
        with self.conn:
            if editing:
                cur = self.conn.execute("""
                    UPDATE products
                    SET barcode=?, name=?, category=?, price=?, stock=?,
                        reorder_level=?, expiry=?, updated_at=?
                    WHERE product_id=?
                """, (barcode, data["name"], data["category"], data["price"],
                      data["stock"], data["reorder_level"],
                      data["expiry"], now, data["product_id"]))
                if cur.rowcount == 0:
                    raise ValueError("Product ID was not found.")
            else:
                self.conn.execute("""
                    INSERT INTO products
                    (product_id, barcode, name, category, price, stock,
                     reorder_level, demand, expiry, updated_at)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """, (data["product_id"], barcode, data["name"], data["category"],
                      data["price"], data["stock"], data["reorder_level"],
                      0, data["expiry"], now))

    def delete_product(self, product_id):
        used = self.conn.execute(
            "SELECT (SELECT COUNT(*) FROM sales WHERE product_id=?) + "
            "(SELECT COUNT(*) FROM restocks WHERE product_id=?)",
            (product_id, product_id)
        ).fetchone()[0]
        if used:
            raise ValueError("This product has sales or restock history and cannot be deleted.")
        with self.conn:
            cur = self.conn.execute(
                "DELETE FROM products WHERE product_id=?", (product_id,)
            )
            if cur.rowcount == 0:
                raise ValueError("Product was not found.")

    def record_sale(self, product_id, quantity):
        with self.conn:
            product = self.conn.execute(
                "SELECT * FROM products WHERE product_id=?", (product_id,)
            ).fetchone()
            if not product:
                raise ValueError("Product was not found.")
            if quantity <= 0:
                raise ValueError("Quantity must be greater than zero.")
            if product["stock"] < quantity:
                raise ValueError(f"Only {product['stock']} unit(s) are available.")
            total = product["price"] * quantity
            self.conn.execute(
                "UPDATE products SET stock=stock-?, updated_at=? WHERE product_id=?",
                (quantity, datetime.now().strftime("%Y-%m-%d %H:%M"), product_id)
            )
            self.conn.execute("""
                INSERT INTO sales
                (product_id, product_name, quantity, unit_price, total, sale_date)
                VALUES (?, ?, ?, ?, ?, ?)
            """, (product_id, product["name"], quantity, product["price"],
                  total, datetime.now().strftime("%Y-%m-%d %H:%M:%S")))
        return total

    def all_sales(self):
        return self.conn.execute(
            "SELECT * FROM sales ORDER BY sale_id DESC"
        ).fetchall()

    def record_restock(self, product_id, quantity, supplier="", unit_cost=None):
        """Add received stock to a product and keep a record of it. Returns the new stock."""
        with self.conn:
            product = self.conn.execute(
                "SELECT * FROM products WHERE product_id=?", (product_id,)
            ).fetchone()
            if not product:
                raise ValueError("Product was not found.")
            if quantity <= 0:
                raise ValueError("Quantity must be greater than zero.")
            if unit_cost is not None and unit_cost < 0:
                raise ValueError("Unit cost cannot be negative.")
            now = datetime.now()
            self.conn.execute(
                "UPDATE products SET stock=stock+?, updated_at=? WHERE product_id=?",
                (quantity, now.strftime("%Y-%m-%d %H:%M"), product_id)
            )
            self.conn.execute("""
                INSERT INTO restocks
                (product_id, product_name, quantity, unit_cost, total_cost,
                 supplier, restock_date)
                VALUES (?, ?, ?, ?, ?, ?, ?)
            """, (product_id, product["name"], quantity, unit_cost,
                  (unit_cost or 0) * quantity, supplier or None,
                  now.strftime("%Y-%m-%d %H:%M:%S")))
        return product["stock"] + quantity

    def all_restocks(self):
        return self.conn.execute(
            "SELECT * FROM restocks ORDER BY restock_id DESC"
        ).fetchall()

    def demand_stats(self, days=DEMAND_WINDOW_DAYS):
        """Units sold per product over the last `days` days: {product_id: units}."""
        cutoff = (datetime.now() - timedelta(days=days)).strftime("%Y-%m-%d %H:%M:%S")
        rows = self.conn.execute(
            "SELECT product_id, SUM(quantity) AS units FROM sales "
            "WHERE sale_date >= ? GROUP BY product_id", (cutoff,)
        ).fetchall()
        return {row["product_id"]: row["units"] for row in rows}

    def close(self):
        self.conn.close()


# ------------------------- MAIN APPLICATION -------------------------

class InventoryApp:
    def __init__(self, root):
        self.root = root
        self.db = InventoryDB()
        self.avl = AVLTree()
        self.avl_root = None
        self.trie = ProductTrie()
        self.priority_heap = []
        self.products_cache = []
        self.style = ttk.Style()
        try:
            self.style.theme_use("clam")
        except tk.TclError:
            pass
        self.configure_styles()
        self.show_login()
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)

    def configure_styles(self):
        self.root.configure(bg=BG)
        self.style.configure("TFrame", background=BG)
        self.style.configure("TLabel", background=BG, foreground=TEXT, font=("Segoe UI", 10))
        self.style.configure("Title.TLabel", background=BG, foreground=NAVY,
                             font=("Segoe UI", 20, "bold"))
        self.style.configure("Sub.TLabel", background=BG, foreground=MUTED,
                             font=("Segoe UI", 10))
        self.style.configure("TButton", font=("Segoe UI", 9, "bold"), padding=(10, 7))
        self.style.configure("Accent.TButton", background=RED, foreground=WHITE)
        self.style.map("Accent.TButton",
                       background=[("active", DARK_RED)],
                       foreground=[("active", WHITE)])
        self.style.configure("Treeview", rowheight=28, font=("Segoe UI", 9),
                             background=WHITE, fieldbackground=WHITE)
        self.style.map("Treeview", background=[("selected", RED)],
                       foreground=[("selected", WHITE)])
        self.style.configure("Treeview.Heading", font=("Segoe UI", 9, "bold"),
                             background="#E4EAF6", foreground=NAVY, padding=7)
        self.style.configure("TNotebook", background=BG, borderwidth=0)
        self.style.configure("TNotebook.Tab", padding=(15, 9), font=("Segoe UI", 9, "bold"))
        # Tab strip is hidden: navigation lives in the top bar instead.
        self.style.layout("Tabless.TNotebook", [("Notebook.client", {"sticky": "nswe"})])
        self.style.layout("Tabless.TNotebook.Tab", [])
        self.style.configure("Tabless.TNotebook", background=BG, borderwidth=0)

    def show_login(self):
        self.login_frame = tk.Frame(self.root, bg=BG)
        self.login_frame.pack(fill="both", expand=True)
        tk.Frame(self.login_frame, bg=RED, height=4).pack(fill="x", side="top")
        panel = tk.Frame(self.login_frame, bg=WHITE, padx=38, pady=32,
                         highlightbackground="#DDE5F0", highlightthickness=1)
        panel.place(relx=0.5, rely=0.5, anchor="center")
        logo = tk.Canvas(panel, width=76, height=76, bg=WHITE, highlightthickness=0)
        logo.pack(anchor="w")
        draw_web_logo(logo, 76)
        tk.Label(panel, text="SPIDER", bg=WHITE, fg=RED,
                 font=("Segoe UI", 11, "bold")).pack(anchor="w", pady=(6, 0))
        tk.Label(panel, text="Welcome back", bg=WHITE, fg=NAVY,
                 font=("Segoe UI", 23, "bold")).pack(anchor="w", pady=(8, 3))
        tk.Label(panel, text="Sign in to manage your inventory", bg=WHITE,
                 fg=MUTED, font=("Segoe UI", 10)).pack(anchor="w", pady=(0, 22))

        tk.Label(panel, text="Username", bg=WHITE, fg=TEXT,
                 font=("Segoe UI", 9, "bold")).pack(anchor="w")
        self.username_var = tk.StringVar(value="admin")
        user_entry = ttk.Entry(panel, textvariable=self.username_var, width=34)
        user_entry.pack(fill="x", ipady=6, pady=(5, 14))

        tk.Label(panel, text="Password", bg=WHITE, fg=TEXT,
                 font=("Segoe UI", 9, "bold")).pack(anchor="w")
        self.password_var = tk.StringVar()
        pass_entry = ttk.Entry(panel, textvariable=self.password_var, show="*", width=34)
        pass_entry.pack(fill="x", ipady=6, pady=(5, 18))
        ttk.Button(panel, text="SIGN IN", style="Accent.TButton",
                   command=self.login).pack(fill="x")
        tk.Label(panel, text="Demo login: admin  /  admin123", bg=WHITE,
                 fg=MUTED, font=("Segoe UI", 8)).pack(anchor="w", pady=(14, 0))
        pass_entry.bind("<Return>", lambda _e: self.login())
        user_entry.focus_set()

    def login(self):
        username = self.username_var.get().strip()
        password_hash = hashlib.sha256(
            self.password_var.get().encode("utf-8")
        ).hexdigest()
        if username == ADMIN_USERNAME and password_hash == ADMIN_PASSWORD_HASH:
            self.login_frame.destroy()
            self.build_main_ui()
        else:
            messagebox.showerror("Login failed", "Incorrect username or password.")

    def build_main_ui(self):
        self.product_search = tk.StringVar()
        tk.Frame(self.root, bg=RED, height=4).pack(fill="x")
        header = tk.Frame(self.root, bg=WHITE, height=72)
        header.pack(fill="x")
        header.pack_propagate(False)
        tk.Frame(self.root, bg="#E3E8F1", height=1).pack(fill="x")

        logo = tk.Canvas(header, width=54, height=54, bg=WHITE, highlightthickness=0)
        logo.pack(side="left", padx=(22, 6), pady=9)
        draw_web_logo(logo, 54)
        tk.Label(header, text="SPIDER", bg=WHITE, fg=NAVY,
                 font=("Segoe UI", 15, "bold")).pack(side="left", padx=(0, 20))

        self.nav_items = []
        nav = tk.Frame(header, bg=WHITE)
        nav.pack(side="left", fill="y")
        for index, name in enumerate(["DASHBOARD", "PRODUCTS", "SALES", "RESTOCK", "ALERTS", "REPORTS"]):
            item = tk.Frame(nav, bg=WHITE, cursor="hand2")
            item.pack(side="left", fill="y", padx=2)
            underline = tk.Frame(item, bg=WHITE, height=3)
            underline.pack(side="bottom", fill="x")
            label = tk.Label(item, text=name, bg=WHITE, fg=NAVY, padx=9,
                             font=("Segoe UI", 10, "bold"), cursor="hand2")
            label.pack(expand=True)
            for widget in (item, label):
                widget.bind("<Button-1>", lambda _e, i=index: self.notebook.select(i))
                widget.bind("<Enter>", lambda _e, l=label: l.configure(fg=RED))
                widget.bind("<Leave>", lambda _e: self.update_nav())
            self.nav_items.append((label, underline))

        logout = tk.Label(header, text="Logout", bg=WHITE, fg=NAVY, cursor="hand2",
                          font=("Segoe UI", 9, "bold"))
        logout.pack(side="right", padx=(8, 22))
        logout.bind("<Button-1>", lambda _e: self.logout())
        logout.bind("<Enter>", lambda _e: logout.configure(fg=RED))
        logout.bind("<Leave>", lambda _e: logout.configure(fg=NAVY))
        tk.Label(header, text="\U0001F464 Admin", bg=WHITE, fg=NAVY,
                 font=("Segoe UI", 9, "bold")).pack(side="right", padx=8)

        search_box = tk.Frame(header, bg=SEARCH_BG)
        search_box.pack(side="left", fill="x", expand=True, padx=22, pady=16)
        tk.Label(search_box, text="\U0001F50D", bg=SEARCH_BG, fg=MUTED).pack(
            side="left", padx=(12, 4))
        self.header_search = tk.Entry(search_box, bd=0, relief="flat", bg=SEARCH_BG,
                                     fg=MUTED, insertbackground=NAVY,
                                     font=("Segoe UI", 10))
        self.header_search.pack(side="left", fill="x", expand=True, ipady=7, padx=(0, 10))
        self.search_placeholder_on = True
        self.header_search.insert(0, SEARCH_HINT)
        self.header_search.bind("<FocusIn>", self.search_focus_in)
        self.header_search.bind("<FocusOut>", self.search_focus_out)
        self.header_search.bind("<KeyRelease>", self.search_typed)

        self.notebook = ttk.Notebook(self.root, style="Tabless.TNotebook")
        self.notebook.pack(fill="both", expand=True, padx=16, pady=14)
        self.dashboard_tab = ttk.Frame(self.notebook, padding=14)
        self.products_tab = ttk.Frame(self.notebook, padding=14)
        self.sales_tab = ttk.Frame(self.notebook, padding=14)
        self.restock_tab = ttk.Frame(self.notebook, padding=14)
        self.alerts_tab = ttk.Frame(self.notebook, padding=14)
        self.reports_tab = ttk.Frame(self.notebook, padding=14)
        self.notebook.add(self.dashboard_tab, text="Dashboard")
        self.notebook.add(self.products_tab, text="Products")
        self.notebook.add(self.sales_tab, text="Sales & Billing")
        self.notebook.add(self.restock_tab, text="Restock")
        self.notebook.add(self.alerts_tab, text="Smart Alerts")
        self.notebook.add(self.reports_tab, text="Reports")
        self.notebook.bind("<<NotebookTabChanged>>", lambda _e: self.update_nav())
        self.update_nav()

        self.build_dashboard_tab()
        self.build_products_tab()
        self.build_sales_tab()
        self.build_restock_tab()
        self.build_alerts_tab()
        self.build_reports_tab()
        self.refresh_all()

    def update_nav(self):
        """Highlight the active top-bar link with a red underline."""
        try:
            current = self.notebook.index("current")
        except tk.TclError:
            return
        for i, (label, underline) in enumerate(self.nav_items):
            active = i == current
            label.configure(fg=RED if active else NAVY)
            underline.configure(bg=RED if active else WHITE)

    def search_focus_in(self, _event=None):
        if self.search_placeholder_on:
            self.header_search.delete(0, "end")
            self.header_search.configure(fg=TEXT)
            self.search_placeholder_on = False

    def search_focus_out(self, _event=None):
        if not self.header_search.get().strip():
            self.header_search.delete(0, "end")
            self.header_search.insert(0, SEARCH_HINT)
            self.header_search.configure(fg=MUTED)
            self.search_placeholder_on = True
            self.product_search.set("")
            self.refresh_products()

    def search_typed(self, _event=None):
        if self.search_placeholder_on:
            return
        self.product_search.set(self.header_search.get())
        self.notebook.select(self.products_tab)
        self.refresh_products()

    def logout(self):
        for widget in self.root.winfo_children():
            widget.destroy()
        self.show_login()

    # ------------------------- DASHBOARD -------------------------

    def build_dashboard_tab(self):
        ttk.Label(self.dashboard_tab, text="Business Overview",
                  style="Title.TLabel").pack(anchor="w")
        ttk.Label(self.dashboard_tab, text="Live summary of products, stock and sales",
                  style="Sub.TLabel").pack(anchor="w", pady=(2, 14))
        # Promo-style banner (spider-sense alert summary)
        banner = tk.Frame(self.dashboard_tab, bg=BANNER_BG, padx=28, pady=16,
                          highlightbackground="#F6C9C4", highlightthickness=1)
        banner.pack(fill="x", pady=(0, 14))
        banner_logo = tk.Canvas(banner, width=84, height=84, bg=BANNER_BG,
                                highlightthickness=0)
        banner_logo.pack(side="right", padx=(18, 0))
        draw_web_logo(banner_logo, 84)
        coupon = tk.Frame(banner, bg=WHITE, padx=24, pady=10)
        coupon.pack(side="right")
        tk.Label(coupon, text="SPIDER-SENSE", bg=WHITE, fg=MUTED,
                 font=("Segoe UI", 9, "bold")).pack(anchor="w")
        tk.Label(coupon, text="RESTOCK ALERT", bg=WHITE, fg=NAVY,
                 font=("Segoe UI", 20, "bold")).pack(anchor="w")
        text_box = tk.Frame(banner, bg=BANNER_BG)
        text_box.pack(side="left")
        self.banner_title = tk.Label(text_box, text="", bg=BANNER_BG, fg=RED,
                                     font=("Segoe UI", 24, "bold"))
        self.banner_title.pack(anchor="w")
        self.banner_sub = tk.Label(text_box, text="", bg=BANNER_BG, fg=NAVY,
                                   font=("Segoe UI", 11))
        self.banner_sub.pack(anchor="w", pady=(2, 0))

        self.cards_frame = ttk.Frame(self.dashboard_tab)
        self.cards_frame.pack(fill="x")
        self.card_values = {}
        card_specs = [
            ("Total Products", "products", BLUE),
            ("Units in Stock", "stock", CYAN),
            ("Low Stock Items", "low", RED),
            ("Sales Revenue", "revenue", GREEN),
        ]
        for title, key, color in card_specs:
            card = tk.Frame(self.cards_frame, bg=WHITE,
                            highlightbackground="#E2E8F0", highlightthickness=1)
            card.pack(side="left", fill="both", expand=True, padx=(0, 10))
            tk.Frame(card, bg=color, height=4).pack(fill="x")
            inner = tk.Frame(card, bg=WHITE, padx=18, pady=13)
            inner.pack(fill="both", expand=True)
            tk.Label(inner, text=title.upper(), bg=WHITE, fg=MUTED,
                     font=("Segoe UI", 8, "bold")).pack(anchor="w")
            value = tk.Label(inner, text="0", bg=WHITE, fg=color,
                             font=("Segoe UI", 22, "bold"))
            value.pack(anchor="w", pady=(5, 0))
            self.card_values[key] = value

        lower = ttk.Frame(self.dashboard_tab)
        lower.pack(fill="both", expand=True, pady=(18, 0))
        chart_box = tk.Frame(lower, bg=WHITE, padx=14, pady=12,
                             highlightbackground="#E2E8F0", highlightthickness=1)
        chart_box.pack(side="left", fill="both", expand=True, padx=(0, 10))
        tk.Label(chart_box, text="STOCK BY CATEGORY", bg=WHITE, fg=NAVY,
                 font=("Segoe UI", 10, "bold")).pack(anchor="w")
        self.chart = tk.Canvas(chart_box, bg=WHITE, height=290, highlightthickness=0)
        self.chart.pack(fill="both", expand=True, pady=(8, 0))
        quick = tk.Frame(lower, bg=WHITE, width=250, padx=14, pady=12,
                         highlightbackground="#E2E8F0", highlightthickness=1)
        quick.pack(side="right", fill="y")
        quick.pack_propagate(False)
        tk.Label(quick, text="QUICK ACTIONS", bg=WHITE, fg=NAVY,
                 font=("Segoe UI", 10, "bold")).pack(anchor="w", pady=(0, 10))
        ttk.Button(quick, text="＋ Add Product", command=self.add_product).pack(fill="x", pady=4)
        ttk.Button(quick, text="＋ Record Sale",
                   command=lambda: self.notebook.select(self.sales_tab)).pack(fill="x", pady=4)
        ttk.Button(quick, text="＋ Record Restock",
                   command=lambda: self.notebook.select(self.restock_tab)).pack(fill="x", pady=4)
        ttk.Button(quick, text="View Smart Alerts",
                   command=lambda: self.notebook.select(self.alerts_tab)).pack(fill="x", pady=4)
        ttk.Button(quick, text="Export Inventory CSV",
                   command=self.export_inventory).pack(fill="x", pady=4)
        tk.Label(quick, text="Data is saved automatically\nin your local SQLite database.",
                 bg=WHITE, fg=MUTED, justify="left",
                 font=("Segoe UI", 8)).pack(anchor="w", pady=(20, 0))

    def safe_draw_chart(self):
        # The chart may be gone if the user logged out within the 100 ms delay.
        try:
            if self.chart.winfo_exists():
                self.draw_category_chart()
        except tk.TclError:
            pass

    def draw_category_chart(self):
        self.chart.delete("all")
        width = max(self.chart.winfo_width(), 500)
        height = max(self.chart.winfo_height(), 260)
        rows = self.db.conn.execute("""
            SELECT category, SUM(stock) AS units
            FROM products GROUP BY category ORDER BY units DESC
        """).fetchall()
        if not rows:
            self.chart.create_text(width / 2, height / 2, text="No inventory data",
                                   fill=MUTED, font=("Segoe UI", 11))
            return
        max_value = max(row["units"] for row in rows) or 1
        left, right, top, bottom = 48, width - 18, 24, height - 48
        self.chart.create_line(left, top, left, bottom, fill="#CBD5E1")
        self.chart.create_line(left, bottom, right, bottom, fill="#CBD5E1")
        slot = (right - left) / len(rows)
        bar_width = min(52, slot * 0.55)
        palette = [RED, BLUE, NAVY, CYAN, DARK_RED, "#64748B"]
        for i, row in enumerate(rows):
            x = left + slot * i + slot / 2
            bar_height = (bottom - top - 18) * row["units"] / max_value
            y = bottom - bar_height
            color = palette[i % len(palette)]
            self.chart.create_rectangle(x - bar_width / 2, y, x + bar_width / 2,
                                        bottom, fill=color, outline="")
            self.chart.create_text(x, y - 10, text=str(row["units"]),
                                   fill=TEXT, font=("Segoe UI", 8, "bold"))
            label = row["category"]
            if len(label) > 11:
                label = label[:10] + "…"
            self.chart.create_text(x, bottom + 18, text=label,
                                   fill=MUTED, font=("Segoe UI", 8))

    # ------------------------- PRODUCTS -------------------------

    def build_products_tab(self):
        top = ttk.Frame(self.products_tab)
        top.pack(fill="x")
        ttk.Label(top, text="Product Inventory", style="Title.TLabel").pack(side="left")
        actions = ttk.Frame(self.products_tab)
        actions.pack(fill="x", pady=(12, 10))
        ttk.Button(actions, text="Add Product", style="Accent.TButton",
                   command=self.add_product).pack(side="left", padx=(0, 6))
        ttk.Button(actions, text="Edit Selected",
                   command=self.edit_selected_product).pack(side="left", padx=3)
        ttk.Button(actions, text="Delete Selected",
                   command=self.delete_selected_product).pack(side="left", padx=3)
        ttk.Button(actions, text="Refresh",
                   command=self.refresh_products).pack(side="right")
        columns = ("id", "name", "category", "price", "stock", "reorder", "demand", "sold", "expiry")
        self.product_tree = ttk.Treeview(self.products_tab, columns=columns,
                                         show="headings", height=18)
        headings = {
            "id": ("Product ID", 90), "name": ("Product Name", 190),
            "category": ("Category", 120), "price": ("Price (₹)", 95),
            "stock": ("Stock", 70), "reorder": ("Reorder Level", 100),
            "demand": ("Demand (0-10)", 105), "sold": ("Sold (30d)", 85),
            "expiry": ("Expiry", 100)
        }
        for col, (label, size) in headings.items():
            self.product_tree.heading(col, text=label)
            self.product_tree.column(col, width=size, anchor="center")
        self.product_tree.tag_configure("low", foreground=RED)
        self.product_tree.pack(fill="both", expand=True)
        self.product_tree.bind("<Double-1>", lambda _e: self.edit_selected_product())

    def add_product(self):
        self.product_dialog()

    def selected_product_id(self):
        # Rows use the product ID as their item id, so IDs like "0012" stay exact.
        selected = self.product_tree.selection() if hasattr(self, "product_tree") else ()
        return selected[0] if selected else None

    def edit_selected_product(self):
        product_id = self.selected_product_id()
        if not product_id:
            messagebox.showinfo("Select product", "Select a product row first.")
            return
        product = self.db.get_product(product_id)
        if product:
            self.product_dialog(product)

    def delete_selected_product(self):
        product_id = self.selected_product_id()
        if not product_id:
            messagebox.showinfo("Select product", "Select a product row first.")
            return
        if messagebox.askyesno("Confirm delete", f"Delete product {product_id}?"):
            try:
                self.db.delete_product(product_id)
                self.refresh_all()
                messagebox.showinfo("Deleted", "Product deleted successfully.")
            except Exception as exc:
                messagebox.showerror("Cannot delete", str(exc))

    def product_dialog(self, product=None):
        editing = product is not None
        win = tk.Toplevel(self.root)
        win.title("Edit Product" if editing else "Add Product")
        win.configure(bg=BG)
        win.resizable(False, False)
        win.transient(self.root)
        win.grab_set()
        frame = tk.Frame(win, bg=WHITE, padx=22, pady=20,
                         highlightbackground="#DDE5F0", highlightthickness=1)
        frame.pack(padx=14, pady=14)
        tk.Label(frame, text="EDIT PRODUCT" if editing else "ADD NEW PRODUCT",
                 bg=WHITE, fg=NAVY, font=("Segoe UI", 14, "bold")).grid(
                     row=0, column=0, columnspan=2, sticky="w", pady=(0, 14))
        fields = [
            ("Product ID", "product_id"), ("Barcode (optional)", "barcode"),
            ("Product Name", "name"), ("Category", "category"),
            ("Price (₹)", "price"), ("Stock Quantity", "stock"),
            ("Reorder Level", "reorder_level"),
            ("Expiry Date (YYYY-MM-DD, optional)", "expiry")
        ]
        vars_ = {}
        for idx, (label, key) in enumerate(fields, start=1):
            tk.Label(frame, text=label, bg=WHITE, fg=TEXT,
                     font=("Segoe UI", 9, "bold")).grid(
                         row=idx, column=0, sticky="w", pady=5, padx=(0, 14))
            default = ""
            if product:
                default = str(product[key]) if product[key] is not None else ""
            elif key == "reorder_level":
                default = "5"
            var = tk.StringVar(value=default)
            vars_[key] = var
            entry = ttk.Entry(frame, textvariable=var, width=32)
            entry.grid(row=idx, column=1, sticky="ew", pady=5, ipady=3)
            if editing and key == "product_id":
                entry.configure(state="disabled")

        tk.Label(frame, text="Demand score is calculated automatically from the last "
                             f"{DEMAND_WINDOW_DAYS} days of sales.",
                 bg=WHITE, fg=MUTED, font=("Segoe UI", 8)).grid(
                     row=len(fields) + 1, column=0, columnspan=2, sticky="w", pady=(6, 0))

        def save():
            try:
                data = {key: var.get().strip() for key, var in vars_.items()}
                if not data["product_id"] or not data["name"] or not data["category"]:
                    raise ValueError("Product ID, name and category are required.")
                try:
                    data["price"] = float(data["price"])
                    data["stock"] = int(data["stock"])
                    data["reorder_level"] = int(data["reorder_level"])
                except ValueError:
                    raise ValueError("Price must be numeric; stock and reorder level must be whole numbers.")
                if data["price"] < 0 or min(data["stock"], data["reorder_level"]) < 0:
                    raise ValueError("Numbers cannot be negative.")
                if data["expiry"]:
                    datetime.strptime(data["expiry"], "%Y-%m-%d")
                self.db.save_product(data, editing=editing)
                win.destroy()
                self.refresh_all()
                messagebox.showinfo("Saved", "Product details saved successfully.")
            except sqlite3.IntegrityError as exc:
                messagebox.showerror("Duplicate value", "Product ID or barcode already exists.")
            except Exception as exc:
                messagebox.showerror("Invalid product", str(exc))

        buttons = ttk.Frame(frame)
        buttons.grid(row=len(fields) + 2, column=0, columnspan=2, sticky="e", pady=(15, 0))
        ttk.Button(buttons, text="Cancel", command=win.destroy).pack(side="right", padx=(6, 0))
        ttk.Button(buttons, text="Save Product", style="Accent.TButton",
                   command=save).pack(side="right")
        win.update_idletasks()
        win.geometry(f"+{self.root.winfo_rootx()+100}+{self.root.winfo_rooty()+70}")

    def refresh_products(self):
        if not hasattr(self, "product_tree"):
            return
        query = self.product_search.get().strip().lower()
        self.product_tree.delete(*self.product_tree.get_children())
        names = [row["name"] for row in self.products_cache]
        self.trie.build(names)
        prefix_matches = set(self.trie.search_prefix(query)) if query else set(names)
        for p in self.products_cache:
            if query and query not in str(p["product_id"]).lower() and p["name"] not in prefix_matches and query not in p["category"].lower():
                continue
            self.product_tree.insert("", "end", iid=p["product_id"], values=(
                p["product_id"], p["name"], p["category"], f"{p['price']:.2f}",
                p["stock"], p["reorder_level"], p["demand"], p["sold_30d"],
                p["expiry"] or "-"
            ), tags=("low",) if p["stock"] <= p["reorder_level"] else ())

    # ------------------------- SALES -------------------------

    def build_sales_tab(self):
        ttk.Label(self.sales_tab, text="Sales & Billing", style="Title.TLabel").pack(anchor="w")
        ttk.Label(self.sales_tab, text="Record a sale to automatically update stock levels",
                  style="Sub.TLabel").pack(anchor="w", pady=(2, 12))
        form = tk.Frame(self.sales_tab, bg=WHITE, padx=16, pady=14,
                        highlightbackground="#E2E8F0", highlightthickness=1)
        form.pack(fill="x", pady=(0, 12))
        tk.Label(form, text="Product", bg=WHITE, fg=TEXT,
                 font=("Segoe UI", 9, "bold")).grid(row=0, column=0, sticky="w")
        self.sale_product_var = tk.StringVar()
        self.sale_product_combo = ttk.Combobox(form, textvariable=self.sale_product_var,
                                               state="readonly", width=42)
        self.sale_product_combo.grid(row=1, column=0, padx=(0, 15), pady=6, ipady=4)
        tk.Label(form, text="Quantity", bg=WHITE, fg=TEXT,
                 font=("Segoe UI", 9, "bold")).grid(row=0, column=1, sticky="w")
        self.sale_quantity_var = tk.StringVar(value="1")
        ttk.Entry(form, textvariable=self.sale_quantity_var, width=12).grid(
            row=1, column=1, padx=(0, 15), pady=6, ipady=4)
        ttk.Button(form, text="Complete Sale", style="Accent.TButton",
                   command=self.record_sale).grid(row=1, column=2, pady=6)
        ttk.Label(self.sales_tab, text="Recent Transactions",
                  font=("Segoe UI", 11, "bold")).pack(anchor="w", pady=(3, 7))
        columns = ("sale_id", "date", "product", "quantity", "unit_price", "total")
        self.sales_tree = ttk.Treeview(self.sales_tab, columns=columns, show="headings", height=15)
        titles = [("sale_id", "Sale ID", 70), ("date", "Date", 155),
                  ("product", "Product", 220), ("quantity", "Quantity", 85),
                  ("unit_price", "Unit Price", 100), ("total", "Total", 110)]
        for col, title, width in titles:
            self.sales_tree.heading(col, text=title)
            self.sales_tree.column(col, width=width, anchor="center")
        self.sales_tree.pack(fill="both", expand=True)

    def record_sale(self):
        if not hasattr(self, "sale_product_combo"):
            messagebox.showinfo("Open application", "Open the Sales & Billing tab first.")
            return
        choice = self.sale_product_var.get()
        if not choice:
            messagebox.showwarning("Select product", "Choose a product before recording a sale.")
            return
        try:
            try:
                quantity = int(self.sale_quantity_var.get())
            except ValueError:
                raise ValueError("Quantity must be a whole number.")
            product_id = choice.split(" | ", 1)[0]
            total = self.db.record_sale(product_id, quantity)
            self.refresh_all()
            messagebox.showinfo("Sale completed", f"Sale recorded successfully.\nTotal: ₹{total:,.2f}")
        except Exception as exc:
            messagebox.showerror("Sale not completed", str(exc))

    def refresh_sales(self):
        self.sales_tree.delete(*self.sales_tree.get_children())
        for sale in self.db.all_sales():
            self.sales_tree.insert("", "end", values=(
                sale["sale_id"], sale["sale_date"], sale["product_name"],
                sale["quantity"], f"₹{sale['unit_price']:.2f}", f"₹{sale['total']:.2f}"
            ))
        options = [f"{p['product_id']} | {p['name']} (Stock: {p['stock']})"
                   for p in self.products_cache]
        current = self.sale_product_var.get()
        self.sale_product_combo["values"] = options
        if current and current.split(" | ", 1)[0] in [p["product_id"] for p in self.products_cache]:
            self.sale_product_var.set(next(
                item for item in options if item.startswith(current.split(" | ", 1)[0] + " | ")
            ))
        elif options:
            self.sale_product_var.set(options[0])
        else:
            self.sale_product_var.set("")

    # ------------------------- RESTOCK -------------------------

    def build_restock_tab(self):
        ttk.Label(self.restock_tab, text="Restock Records",
                  style="Title.TLabel").pack(anchor="w")
        ttk.Label(self.restock_tab,
                  text="Record stock received from suppliers to add it back to inventory",
                  style="Sub.TLabel").pack(anchor="w", pady=(2, 12))
        form = tk.Frame(self.restock_tab, bg=WHITE, padx=16, pady=14,
                        highlightbackground="#E2E8F0", highlightthickness=1)
        form.pack(fill="x", pady=(0, 12))
        for col, text in enumerate(["Product", "Quantity received",
                                    "Unit cost (₹, optional)", "Supplier (optional)"]):
            tk.Label(form, text=text, bg=WHITE, fg=TEXT,
                     font=("Segoe UI", 9, "bold")).grid(row=0, column=col, sticky="w")
        self.restock_product_var = tk.StringVar()
        self.restock_combo = ttk.Combobox(form, textvariable=self.restock_product_var,
                                          state="readonly", width=36)
        self.restock_combo.grid(row=1, column=0, padx=(0, 15), pady=6, ipady=4)
        self.restock_combo.bind("<<ComboboxSelected>>",
                                lambda _e: self.update_restock_hint(fill_quantity=True))
        self.restock_qty_var = tk.StringVar(value="1")
        ttk.Entry(form, textvariable=self.restock_qty_var, width=14).grid(
            row=1, column=1, padx=(0, 15), pady=6, ipady=4)
        self.restock_cost_var = tk.StringVar()
        ttk.Entry(form, textvariable=self.restock_cost_var, width=16).grid(
            row=1, column=2, padx=(0, 15), pady=6, ipady=4)
        self.restock_supplier_var = tk.StringVar()
        ttk.Entry(form, textvariable=self.restock_supplier_var, width=24).grid(
            row=1, column=3, padx=(0, 15), pady=6, ipady=4)
        ttk.Button(form, text="Record Restock", style="Accent.TButton",
                   command=self.record_restock).grid(row=1, column=4, pady=6)
        self.restock_hint = tk.Label(form, text="", bg=WHITE, fg=MUTED,
                                     font=("Segoe UI", 9))
        self.restock_hint.grid(row=2, column=0, columnspan=5, sticky="w")
        ttk.Label(self.restock_tab, text="Restock History",
                  font=("Segoe UI", 11, "bold")).pack(anchor="w", pady=(3, 7))
        columns = ("id", "date", "product", "quantity", "unit_cost", "total_cost", "supplier")
        self.restock_tree = ttk.Treeview(self.restock_tab, columns=columns,
                                         show="headings", height=14)
        for col, title, width in [
            ("id", "ID", 55), ("date", "Date", 150), ("product", "Product", 190),
            ("quantity", "Quantity", 80), ("unit_cost", "Unit Cost", 95),
            ("total_cost", "Total Cost", 105), ("supplier", "Supplier", 190)
        ]:
            self.restock_tree.heading(col, text=title)
            self.restock_tree.column(col, width=width, anchor="center")
        self.restock_tree.pack(fill="both", expand=True)

    def selected_restock_product(self):
        choice = self.restock_product_var.get()
        if not choice:
            return None
        product_id = choice.split(" | ", 1)[0]
        return next((p for p in self.products_cache if p["product_id"] == product_id), None)

    def update_restock_hint(self, fill_quantity=False):
        p = self.selected_restock_product()
        if not p:
            self.restock_hint.configure(text="")
            return
        suggestion = self.suggested_qty(p)
        if p["days_left"] is None:
            cover = "no sales in the last 30 days"
        else:
            cover = f"about {p['days_left']} day(s) of stock left"
        self.restock_hint.configure(
            text=f"Current stock: {p['stock']}  •  Reorder level: {p['reorder_level']}  •  "
                 f"Sold in last {DEMAND_WINDOW_DAYS} days: {p['sold_30d']} ({cover})  •  "
                 f"Suggested restock: {suggestion}")
        if fill_quantity and suggestion > 0:
            self.restock_qty_var.set(str(suggestion))

    def record_restock(self):
        p = self.selected_restock_product()
        if not p:
            messagebox.showwarning("Select product", "Choose a product to restock.")
            return
        try:
            try:
                quantity = int(self.restock_qty_var.get())
            except ValueError:
                raise ValueError("Quantity must be a whole number.")
            cost_text = self.restock_cost_var.get().strip()
            try:
                unit_cost = float(cost_text) if cost_text else None
            except ValueError:
                raise ValueError("Unit cost must be a number.")
            new_stock = self.db.record_restock(
                p["product_id"], quantity, self.restock_supplier_var.get().strip(), unit_cost)
            self.restock_qty_var.set("1")
            self.restock_cost_var.set("")
            self.refresh_all()
            messagebox.showinfo("Restock recorded",
                                f"{quantity} unit(s) added to {p['name']}.\nNew stock: {new_stock}")
        except Exception as exc:
            messagebox.showerror("Restock not recorded", str(exc))

    def refresh_restock(self):
        self.restock_tree.delete(*self.restock_tree.get_children())
        for r in self.db.all_restocks():
            has_cost = r["unit_cost"] is not None
            self.restock_tree.insert("", "end", values=(
                r["restock_id"], r["restock_date"], r["product_name"], r["quantity"],
                f"₹{r['unit_cost']:.2f}" if has_cost else "-",
                f"₹{r['total_cost']:.2f}" if has_cost else "-",
                r["supplier"] or "-"
            ))
        options = [f"{p['product_id']} | {p['name']} (Stock: {p['stock']})"
                   for p in self.products_cache]
        current = self.restock_product_var.get()
        self.restock_combo["values"] = options
        keep = current.split(" | ", 1)[0] + " | " if current else None
        match = next((o for o in options if keep and o.startswith(keep)), None)
        self.restock_product_var.set(match or (options[0] if options else ""))
        self.update_restock_hint()

    def open_restock_for(self, product_id, quantity=None):
        for item in self.restock_combo["values"]:
            if item.startswith(f"{product_id} | "):
                self.restock_product_var.set(item)
                break
        if quantity:
            self.restock_qty_var.set(str(quantity))
        self.update_restock_hint()
        self.notebook.select(self.restock_tab)

    # ------------------------- SMART ALERTS & PRIORITY -------------------------

    def build_alerts_tab(self):
        ttk.Label(self.alerts_tab, text="Smart Alerts & Priority Queue",
                  style="Title.TLabel").pack(anchor="w")
        ttk.Label(self.alerts_tab,
                  text="Items are ranked using demand, stock shortage and expiry urgency",
                  style="Sub.TLabel").pack(anchor="w", pady=(2, 12))
        self.alert_summary = ttk.Label(self.alerts_tab, text="")
        self.alert_summary.pack(anchor="w", pady=(0, 8))
        split = ttk.Frame(self.alerts_tab)
        split.pack(fill="both", expand=True)
        left = ttk.Frame(split)
        right = ttk.Frame(split)
        left.pack(side="left", fill="both", expand=True, padx=(0, 8))
        right.pack(side="left", fill="both", expand=True, padx=(8, 0))
        ttk.Label(left, text="LOW STOCK / EXPIRY ALERTS",
                  font=("Segoe UI", 10, "bold")).pack(anchor="w", pady=(0, 7))
        self.alert_tree = ttk.Treeview(left, columns=("id", "name", "stock", "status"),
                                       show="headings", height=17)
        for col, title, width in [
            ("id", "Product ID", 85), ("name", "Product", 165),
            ("stock", "Stock", 65), ("status", "Alert", 125)
        ]:
            self.alert_tree.heading(col, text=title)
            self.alert_tree.column(col, width=width, anchor="center")
        self.alert_tree.pack(fill="both", expand=True)
        ttk.Label(right, text="RESTOCK PRIORITY RANKING",
                  font=("Segoe UI", 10, "bold")).pack(anchor="w", pady=(0, 7))
        self.priority_tree = ttk.Treeview(
            right, columns=("rank", "id", "name", "score", "days", "suggestion"),
            show="headings", height=17
        )
        for col, title, width in [
            ("rank", "Rank", 45), ("id", "ID", 65), ("name", "Product", 125),
            ("score", "Score", 50), ("days", "Days Left", 70), ("suggestion", "Suggested Qty", 90)
        ]:
            self.priority_tree.heading(col, text=title)
            self.priority_tree.column(col, width=width, anchor="center")
        self.priority_tree.pack(fill="both", expand=True)
        buttons = ttk.Frame(self.alerts_tab)
        buttons.pack(fill="x", pady=(10, 0))
        ttk.Button(buttons, text="Refresh Alerts",
                   command=self.refresh_alerts).pack(side="right")
        ttk.Button(buttons, text="Restock Selected", style="Accent.TButton",
                   command=self.restock_selected_from_alerts).pack(side="right", padx=(0, 8))

    def product_alerts(self, product):
        alerts = []
        if product["stock"] <= product["reorder_level"]:
            alerts.append("LOW STOCK")
        if product["expiry"]:
            try:
                exp = datetime.strptime(product["expiry"], "%Y-%m-%d").date()
                days = (exp - date.today()).days
                if days < 0:
                    alerts.append("EXPIRED")
                elif days <= 30:
                    alerts.append(f"EXPIRY {days} DAYS")
            except ValueError:
                pass
        return alerts

    def priority_score(self, product):
        shortage = max(0, product["reorder_level"] - product["stock"])
        score = product["demand"] * 2 + shortage * 5
        if product["stock"] <= product["reorder_level"]:
            score += 10
        days_left = product.get("days_left")
        if days_left is not None and days_left <= 7:
            score += 8   # selling fast: less than a week of stock left
        if product["expiry"]:
            try:
                days = (datetime.strptime(product["expiry"], "%Y-%m-%d").date() - date.today()).days
                if 0 <= days <= 30:
                    score += (31 - days) * 2
                elif days < 0:
                    score += 50
            except ValueError:
                pass
        return score

    def suggested_qty(self, product):
        """Stock up to the larger of 2x the reorder level or 14 days of recent sales."""
        target = max(product["reorder_level"] * 2, math.ceil(product["daily_rate"] * 14))
        return max(0, target - product["stock"])

    def restock_selected_from_alerts(self):
        selected = self.priority_tree.selection()
        if not selected:
            messagebox.showinfo("Select product", "Select a row in the priority ranking first.")
            return
        product_id = selected[0]
        p = next((x for x in self.products_cache if x["product_id"] == product_id), None)
        self.open_restock_for(product_id, self.suggested_qty(p) if p else None)

    def refresh_alerts(self):
        if not hasattr(self, "alert_tree"):
            return
        self.alert_tree.delete(*self.alert_tree.get_children())
        self.priority_tree.delete(*self.priority_tree.get_children())
        self.priority_heap = []
        alert_count = 0
        for p in self.products_cache:
            alerts = self.product_alerts(p)
            if alerts:
                alert_count += 1
                self.alert_tree.insert("", "end", values=(
                    p["product_id"], p["name"], p["stock"], ", ".join(alerts)
                ))
            score = self.priority_score(p)
            suggestion = self.suggested_qty(p)
            heapq.heappush(self.priority_heap, (-score, p["name"].lower(),
                                                p["product_id"], suggestion))
        self.alert_summary.configure(
            text=f"{alert_count} product(s) need attention  •  {len(self.products_cache)} product(s) ranked"
        )
        by_id = {p["product_id"]: p for p in self.products_cache}
        rank = 1
        while self.priority_heap:
            neg_score, _name, product_id, suggestion = heapq.heappop(self.priority_heap)
            p = by_id[product_id]
            days = "-" if p["days_left"] is None else p["days_left"]
            self.priority_tree.insert("", "end", iid=product_id, values=(
                rank, product_id, p["name"], -neg_score, days, suggestion
            ))
            rank += 1

    # ------------------------- REPORTS -------------------------

    def build_reports_tab(self):
        ttk.Label(self.reports_tab, text="Reports & Data Export",
                  style="Title.TLabel").pack(anchor="w")
        ttk.Label(self.reports_tab, text="Export inventory, sales and restock records as CSV files",
                  style="Sub.TLabel").pack(anchor="w", pady=(2, 15))
        box = tk.Frame(self.reports_tab, bg=WHITE, padx=20, pady=20,
                       highlightbackground="#E2E8F0", highlightthickness=1)
        box.pack(fill="x", anchor="n")
        ttk.Button(box, text="Export Inventory CSV", style="Accent.TButton",
                   command=self.export_inventory).pack(anchor="w", pady=6)
        ttk.Button(box, text="Export Sales CSV",
                   command=self.export_sales).pack(anchor="w", pady=6)
        ttk.Button(box, text="Export Restock CSV",
                   command=self.export_restocks).pack(anchor="w", pady=6)
        ttk.Button(box, text="Generate Text Summary",
                   command=self.generate_text_report).pack(anchor="w", pady=6)
        ttk.Button(box, text="Load Sample Data",
                   command=self.load_sample_data).pack(anchor="w", pady=6)
        self.report_status = ttk.Label(box, text="Choose a report to generate.")
        self.report_status.pack(anchor="w", pady=(12, 0))
        tk.Label(self.reports_tab,
                 text=f"Database file: {os.path.abspath(DB_FILE)}\n"
                      "Keep this file to preserve your products and sales history.",
                 bg=BG, fg=MUTED, justify="left",
                 font=("Segoe UI", 9)).pack(anchor="w", pady=18)

    def export_inventory(self):
        path = filedialog.asksaveasfilename(
            defaultextension=".csv", filetypes=[("CSV files", "*.csv")],
            initialfile="inventory_report.csv"
        )
        if not path:
            return
        rows = self.products_cache
        with open(path, "w", newline="", encoding="utf-8-sig") as file:
            writer = csv.writer(file)
            writer.writerow(["Product ID", "Barcode", "Name", "Category", "Price",
                             "Stock", "Reorder Level", "Demand (0-10)", "Sold (30d)", "Expiry"])
            for p in rows:
                writer.writerow([p["product_id"], p["barcode"], p["name"], p["category"],
                                 p["price"], p["stock"], p["reorder_level"],
                                 p["demand"], p["sold_30d"], p["expiry"]])
        if hasattr(self, "report_status"):
            self.report_status.configure(text=f"Inventory exported: {path}")
        messagebox.showinfo("Export complete", f"Inventory report saved to:\n{path}")

    def export_sales(self):
        path = filedialog.asksaveasfilename(
            defaultextension=".csv", filetypes=[("CSV files", "*.csv")],
            initialfile="sales_report.csv"
        )
        if not path:
            return
        rows = self.db.all_sales()
        with open(path, "w", newline="", encoding="utf-8-sig") as file:
            writer = csv.writer(file)
            writer.writerow(["Sale ID", "Product ID", "Product", "Quantity",
                             "Unit Price", "Total", "Sale Date"])
            for sale in rows:
                writer.writerow([sale["sale_id"], sale["product_id"], sale["product_name"],
                                 sale["quantity"], sale["unit_price"], sale["total"],
                                 sale["sale_date"]])
        if hasattr(self, "report_status"):
            self.report_status.configure(text=f"Sales exported: {path}")
        messagebox.showinfo("Export complete", f"Sales report saved to:\n{path}")

    def export_restocks(self):
        path = filedialog.asksaveasfilename(
            defaultextension=".csv", filetypes=[("CSV files", "*.csv")],
            initialfile="restock_report.csv"
        )
        if not path:
            return
        rows = self.db.all_restocks()
        with open(path, "w", newline="", encoding="utf-8-sig") as file:
            writer = csv.writer(file)
            writer.writerow(["Restock ID", "Product ID", "Product", "Quantity",
                             "Unit Cost", "Total Cost", "Supplier", "Restock Date"])
            for r in rows:
                writer.writerow([r["restock_id"], r["product_id"], r["product_name"],
                                 r["quantity"], r["unit_cost"], r["total_cost"],
                                 r["supplier"], r["restock_date"]])
        if hasattr(self, "report_status"):
            self.report_status.configure(text=f"Restocks exported: {path}")
        messagebox.showinfo("Export complete", f"Restock report saved to:\n{path}")

    def load_sample_data(self):
        if not messagebox.askyesno(
                "Load sample data",
                "Add the demo products, sales and restock records that are missing?\n"
                "Your own data will not be changed."):
            return
        products, sales, restocks = self.db.load_sample_data()
        self.refresh_all()
        messagebox.showinfo("Sample data",
                            f"Added {products} product(s), {sales} sale(s) "
                            f"and {restocks} restock record(s).")

    def generate_text_report(self):
        products = self.db.all_products()
        sales = self.db.all_sales()
        stock_units = sum(p["stock"] for p in products)
        revenue = sum(s["total"] for s in sales)
        low = sum(1 for p in products if p["stock"] <= p["reorder_level"])
        path = filedialog.asksaveasfilename(
            defaultextension=".txt", filetypes=[("Text files", "*.txt")],
            initialfile="inventory_summary.txt"
        )
        if not path:
            return
        with open(path, "w", encoding="utf-8") as file:
            file.write("INTELLIGENT INVENTORY & PRIORITY MANAGEMENT SYSTEM\n")
            file.write("=" * 58 + "\n")
            file.write(f"Generated: {datetime.now():%Y-%m-%d %H:%M}\n")
            file.write(f"Total products: {len(products)}\n")
            file.write(f"Total units in stock: {stock_units}\n")
            file.write(f"Low-stock products: {low}\n")
            file.write(f"Number of sales: {len(sales)}\n")
            file.write(f"Total sales revenue: Rs. {revenue:,.2f}\n")
            restocks = self.db.all_restocks()
            file.write(f"Restock records: {len(restocks)}\n")
            file.write(f"Total restock cost: Rs. "
                       f"{sum(r['total_cost'] for r in restocks):,.2f}\n\n")
            file.write("PRODUCT STOCK DETAILS\n" + "-" * 58 + "\n")
            for p in products:
                file.write(f"{p['product_id']} | {p['name']} | Stock: {p['stock']} | "
                           f"Reorder at: {p['reorder_level']}\n")
        if hasattr(self, "report_status"):
            self.report_status.configure(text=f"Text report saved: {path}")
        messagebox.showinfo("Report generated", f"Summary saved to:\n{path}")

    # ------------------------- REFRESH / CLOSE -------------------------

    def refresh_all(self):
        # Demand score (0-10) is calculated from sales in the last 30 days: the
        # best seller scores 10. A log curve keeps one very fast seller from
        # squashing every other product down to 0 or 1.
        units = self.db.demand_stats(DEMAND_WINDOW_DAYS)
        top = max(units.values(), default=0)
        cache = []
        for row in self.db.all_products():
            p = dict(row)
            sold = units.get(p["product_id"], 0)
            p["sold_30d"] = sold
            p["demand"] = round(10 * math.log1p(sold) / math.log1p(top)) if top else 0
            p["daily_rate"] = sold / DEMAND_WINDOW_DAYS
            p["days_left"] = (int(p["stock"] / p["daily_rate"])
                              if p["daily_rate"] > 0 else None)
            cache.append(p)
        self.products_cache = cache
        self.avl_root = None
        for p in self.products_cache:
            self.avl_root = self.avl.insert(self.avl_root, p["product_id"])
        self.trie.build([p["name"] for p in self.products_cache])
        if hasattr(self, "product_tree"):
            self.refresh_products()
        if hasattr(self, "sales_tree"):
            self.refresh_sales()
        if hasattr(self, "restock_tree"):
            self.refresh_restock()
        if hasattr(self, "alert_tree"):
            self.refresh_alerts()
        if hasattr(self, "card_values"):
            stock = sum(p["stock"] for p in self.products_cache)
            low = sum(1 for p in self.products_cache
                      if p["stock"] <= p["reorder_level"])
            revenue = sum(s["total"] for s in self.db.all_sales())
            self.card_values["products"].configure(text=str(len(self.products_cache)))
            self.card_values["stock"].configure(text=str(stock))
            self.card_values["low"].configure(text=str(low))
            self.card_values["revenue"].configure(text=f"₹{revenue:,.0f}")
            if low:
                self.banner_title.configure(text=f"{low} item(s) need restock")
                self.banner_sub.configure(
                    text="Open Alerts to see the priority ranking and suggested quantities")
            else:
                self.banner_title.configure(text="All stock levels look healthy")
                self.banner_sub.configure(text="No product is at or below its reorder level")
            self.root.after(100, self.safe_draw_chart)

    def on_close(self):
        try:
            self.db.close()
        finally:
            self.root.destroy()


def main():
    if sys.platform.startswith("win"):
        try:  # crisp text on high-DPI Windows screens
            import ctypes
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass
    migrate_legacy_db()
    root = tk.Tk()
    root.title(APP_TITLE)
    try:
        root.iconbitmap(resource_path("app.ico"))
    except tk.TclError:
        pass
    root.geometry("1180x760")
    root.minsize(980, 650)
    InventoryApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
