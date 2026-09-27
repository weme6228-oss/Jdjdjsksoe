# -*- coding: utf-8 -*-
"""
ربات جامع فال، سرگرمی، مکالمه هوشمند و مدیریت گروه تلگرام - نسخه ۳
====================================================================
نصب پیش‌نیازها:
    pip install "python-telegram-bot[job-queue]" requests

قبل از اجرا، این دو متغیر محیطی رو تنظیم کن (توکن رو هاردکد نکن!):
    export BOT_TOKEN="توکن ربات از BotFather"
    export GEMINI_API_KEY="کلید Gemini از Google AI Studio"

اجرا:
    python bot_v3.py
"""

import os
import re
import html
import json
import time
import random
import asyncio
import logging
import unicodedata
import traceback
from pathlib import Path
from datetime import datetime, timedelta
from collections import defaultdict, deque

import requests
from telegram import Update, BotCommand, InlineKeyboardButton, InlineKeyboardMarkup, ChatPermissions
from telegram.ext import (
    ApplicationBuilder,
    CommandHandler,
    MessageHandler,
    CallbackQueryHandler,
    ContextTypes,
    filters,
)
from telegram.error import BadRequest, TelegramError, Forbidden

# ============================================================
# تنظیمات اصلی — از متغیرهای محیطی خونده می‌شه، هرگز داخل کد ننویس
# ============================================================
BOT_TOKEN = os.environ.get("BOT_TOKEN", "").strip()
GEMINI_API_KEY = os.environ.get("GEMINI_API_KEY", "").strip()

GEMINI_MODELS = ["gemini-2.5-flash", "gemini-2.0-flash", "gemini-flash-latest"]
GEMINI_BASE = "https://generativelanguage.googleapis.com/v1beta/models"

DATA_DIR = Path(__file__).parent
BAD_WORDS_FILE = DATA_DIR / "bad_words.json"
WARN_FILE = DATA_DIR / "warns.json"
MEMORY_FILE = DATA_DIR / "chat_memory.json"

MEMORY_MAX_PER_CHAT = 40      # حداکثر پیام ذخیره‌شده برای هر گروه (حافظه رو کوچیک نگه می‌داره)
MEMORY_MAX_AGE_DAYS = 7       # پیام‌های قدیمی‌تر از این، هفته‌ای یک‌بار پاک می‌شن
MEMORY_CONTEXT_LIMIT = 8      # چند پیام اخیر برای ساخت زمینه‌ی مکالمه استفاده بشه

TRIGGER_WORDS = ["ربات", "دستیار"]  # اگه پیام شامل این کلمات باشه، ربات وارد مکالمه می‌شه

logging.basicConfig(
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    level=logging.INFO,
)
logger = logging.getLogger(__name__)

# Session مشترک HTTP - به‌جای باز کردن یه اتصال جدید برای هر درخواست (به گنجور، قیمت‌ها و...)،
# اتصال‌ها reuse می‌شن. این هم سرعت رو بهتر می‌کنه هم مصرف منابع سرور رو کاهش می‌ده.
_http_session = requests.Session()
_http_session.headers.update({"User-Agent": "Mozilla/5.0 (compatible; FalBot/1.0)"})

PRICE_CACHE = {"data": None, "time": None}
CACHE_SECONDS = 90

# کاربرهایی که دکمه «گفتگو با هوش مصنوعی» رو زدن - پیام بعدیشون مستقیم به Gemini می‌ره
# (بدون نیاز به ریپلای یا گفتن کلمه «ربات»)
direct_chat_users = set()  # {"chat_id:user_id"}
FLOOD_WINDOW = 10
FLOOD_LIMIT = 5
user_message_times = defaultdict(lambda: deque(maxlen=FLOOD_LIMIT))

# ============================================================
# لیست کلمات نامناسب
# ============================================================
DEFAULT_BAD_WORDS_FA = [
    "کصکش", "کصکشش", "کیری", "کیر", "جنده", "کونی", "کون",
    "لاشی", "عوضی", "حرومزاده", "مادرجنده", "خارکسه", "گاییدم",
    "کسکش", "ننتو", "زنیکه", "کثافت", "جاکش", "عنتر",
]
DEFAULT_BAD_WORDS_EN = [
    "fuck", "fucking", "shit", "bitch", "asshole", "bastard",
    "cunt", "dick", "pussy", "whore", "slut", "motherfucker", "retard",
]

LEET_MAP = {"0": "o", "1": "i", "3": "e", "4": "a", "5": "s", "7": "t", "@": "a", "$": "s", "!": "i"}


def load_json_safe(path: Path, default):
    if path.exists():
        try:
            with open(path, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception as e:
            logger.warning(f"خطا در خواندن {path}: {e}")
    return default


def save_json_safe(path: Path, data):
    try:
        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
    except Exception as e:
        logger.warning(f"خطا در ذخیره {path}: {e}")


bad_data = load_json_safe(BAD_WORDS_FILE, {"fa": DEFAULT_BAD_WORDS_FA, "en": DEFAULT_BAD_WORDS_EN})
BAD_WORDS_FA = bad_data.get("fa", DEFAULT_BAD_WORDS_FA)
BAD_WORDS_EN = bad_data.get("en", DEFAULT_BAD_WORDS_EN)
if not BAD_WORDS_FILE.exists():
    save_json_safe(BAD_WORDS_FILE, {"fa": BAD_WORDS_FA, "en": BAD_WORDS_EN})

warns_data = load_json_safe(WARN_FILE, {})          # {"chat_id:user_id": count}
chat_memory = load_json_safe(MEMORY_FILE, {})        # {"chat_id": [{"role","name","text","time"}]}


def normalize_text(text: str) -> str:
    text = text.lower()
    text = unicodedata.normalize("NFKC", text)
    text = "".join(LEET_MAP.get(ch, ch) for ch in text)
    text = re.sub(r"[\s\.\-_\*]+", "", text)
    text = re.sub(r"(.)\1{1,}", r"\1", text)
    return text


def contains_bad_word(text: str):
    norm = normalize_text(text)
    for w in [normalize_text(w) for w in BAD_WORDS_FA + BAD_WORDS_EN]:
        if w and w in norm:
            return True
    return False


async def is_admin(update: Update, context: ContextTypes.DEFAULT_TYPE) -> bool:
    chat = update.effective_chat
    user = update.effective_user
    if chat.type == "private":
        return True
    try:
        member = await context.bot.get_chat_member(chat.id, user.id)
        return member.status in ("administrator", "creator")
    except Exception:
        return False


def mention_html(user) -> str:
    """منشن امن با HTML (بر خلاف Markdown، با اسم‌های حاوی کاراکترهای خاص خطا نمی‌ده)."""
    name = html.escape(user.first_name or "کاربر")
    return f'<a href="tg://user?id={user.id}">{name}</a>'


def is_mostly_persian(text: str) -> bool:
    """بررسی می‌کنه که متن عمدتاً فارسی باشه (برای جلوگیری از جواب انگلیسی Gemini)."""
    persian_chars = len(re.findall(r"[آ-ی]", text))
    latin_chars = len(re.findall(r"[a-zA-Z]", text))
    if persian_chars == 0 and latin_chars > 10:
        return False
    return persian_chars >= latin_chars


# ============================================================
# 🧠 بخش اختصاصی Gemini (GEMINI ENGINE) - این کل بخشیه که با سرور گوگل حرف می‌زنه
# همه‌ی درخواست‌های هوش مصنوعی ربات (فال، تاروت، مکالمه، دکمه Gemini و...) از همین
# یه‌جا رد می‌شن. کلید API همینجا استفاده می‌شه و مستقیم به آدرس رسمی گوگل زده می‌شه:
#   https://generativelanguage.googleapis.com/v1beta/models/<model>:generateContent?key=<کلید>
# این یعنی: بله، این بخش واقعاً و مستقیماً به سرورهای Gemini گوگل وصل می‌شه، با همون
# توکنی که دادی. هیچ واسطه یا شبیه‌سازی‌ای در کار نیست.
# ============================================================
def _ask_gemini_blocking(prompt: str, max_tokens: int = 500, temperature: float = 1.0) -> "str | None":
    if not GEMINI_API_KEY:
        logger.warning("GEMINI_API_KEY تنظیم نشده - این درخواست بدون هوش مصنوعی fallback می‌زنه.")
        return None

    full_prompt = (
        "مهم: پاسخ باید کاملاً و فقط به زبان فارسی روان و طبیعی باشه، "
        "هیچ کلمه انگلیسی (مگر اسم خاص ضروری) توش نباشه.\n\n" + prompt
    )
    headers = {"Content-Type": "application/json"}
    payload = {
        "contents": [{"parts": [{"text": full_prompt}]}],
        "generationConfig": {"maxOutputTokens": max_tokens, "temperature": temperature},
    }

    for model in GEMINI_MODELS:
        url = f"{GEMINI_BASE}/{model}:generateContent?key={GEMINI_API_KEY}"
        for attempt in range(2):
            try:
                r = _http_session.post(url, headers=headers, json=payload, timeout=15)
                if r.status_code == 200:
                    data = r.json()
                    candidates = data.get("candidates", [])
                    if not candidates:
                        logger.warning(f"Gemini({model}): کاندید خالی برگشت - {data}")
                        break
                    parts = candidates[0].get("content", {}).get("parts", [])
                    if not parts:
                        logger.warning(f"Gemini({model}): content خالی - {candidates[0]}")
                        break
                    text = parts[0].get("text", "").strip()
                    if not text:
                        break
                    if not is_mostly_persian(text):
                        logger.warning(f"Gemini({model}): پاسخ غیرفارسی بود، رد شد")
                        break
                    return text
                elif r.status_code == 404:
                    logger.warning(f"Gemini({model}): مدل یافت نشد (404)، رفتن به مدل بعدی")
                    break
                elif r.status_code == 400:
                    logger.warning(f"Gemini({model}): درخواست نامعتبر (400) - معمولاً یعنی کلید API اشتباهه یا "
                                    f"فرمت درخواست مشکل داره، نه مشکل فیلترینگ. جزئیات: {r.text[:300]}")
                    break
                elif r.status_code == 402:
                    logger.warning(f"Gemini({model}): نیاز به فعال‌سازی صورتحساب (402) - سهمیه رایگان این کلید "
                                    f"تموم شده یا نیاز به فعال‌سازی Billing توی Google AI Studio داره. جزئیات: {r.text[:300]}")
                    break
                elif r.status_code == 403:
                    logger.warning(f"Gemini({model}): دسترسی رد شد (403) - کلید API غیرفعاله یا محدودیت منطقه‌ای/پروژه داره. "
                                    f"جزئیات: {r.text[:300]}")
                    break
                elif r.status_code in (429, 500, 502, 503):
                    logger.warning(f"Gemini({model}): خطای موقت {r.status_code}، تلاش مجدد")
                    time.sleep(1)
                    continue
                else:
                    logger.warning(f"Gemini({model}): خطای {r.status_code} - {r.text[:300]}")
                    break
            except requests.exceptions.Timeout:
                logger.warning(f"Gemini({model}): timeout در تلاش {attempt + 1}")
                continue
            except Exception as e:
                logger.warning(f"Gemini({model}): خطای غیرمنتظره - {e}")
                break
    return None


async def ask_gemini(prompt: str, max_tokens: int = 500, temperature: float = 1.0) -> "str | None":
    """نسخه‌ی ناهمزمان: فراخوانی شبکه‌ای رو توی یه ترد جدا اجرا می‌کنه تا حلقه‌ی اصلی asyncio
    (و در نتیجه بقیه‌ی گروه‌ها، دستورها و بازی گرگینه که هم‌زمان در جریانن) قفل نشه و منتظر نمونه."""
    return await asyncio.to_thread(_ask_gemini_blocking, prompt, max_tokens, temperature)


# ============================================================
# آرکانای بزرگ (۲۲ کارت) و کوچک (۵۶ کارت) - دک کامل و واقعی
# ============================================================
MAJOR_ARCANA = [
    ("دلقک", "The Fool", "شروع تازه، ماجراجویی و اعتماد به مسیر جدید."),
    ("جادوگر", "The Magician", "قدرت اراده، مهارت و به‌کارگیری استعدادها."),
    ("کاهنه", "The High Priestess", "شهود، رازها و دانش پنهان."),
    ("امپراتریس", "The Empress", "فراوانی، خلاقیت و رشد."),
    ("امپراتور", "The Emperor", "نظم، ساختار و کنترل بر شرایط."),
    ("پاپ / خردمند", "The Hierophant", "سنت، آموزش و راهنمایی معنوی."),
    ("عاشقان", "The Lovers", "انتخاب مهم، هماهنگی و رابطه."),
    ("ارابه", "The Chariot", "اراده قوی، پیروزی با تلاش و کنترل."),
    ("قدرت", "Strength", "شجاعت درونی و کنترل احساسات."),
    ("زاهد", "The Hermit", "درون‌نگری، تنهایی سازنده و جست‌وجوی حقیقت."),
    ("چرخ بخت", "Wheel of Fortune", "تغییر ناگهانی سرنوشت، فرصت‌های تازه."),
    ("عدالت", "Justice", "انصاف، حقیقت و پیامدهای اعمال."),
    ("مرد آویزان", "The Hanged Man", "تعلیق، دیدگاه تازه، فداکاری."),
    ("مرگ", "Death", "پایان یک دوره و آغاز تحول بزرگ."),
    ("اعتدال", "Temperance", "تعادل، صبر و ترکیب هماهنگ."),
    ("اهریمن", "The Devil", "وابستگی، محدودیت‌های خودساخته."),
    ("برج", "The Tower", "تغییر ناگهانی و فروریختن باورهای غلط."),
    ("ستاره", "The Star", "امید، الهام و آرامش پس از سختی."),
    ("ماه", "The Moon", "ابهام، ترس‌های پنهان و ناخودآگاه."),
    ("خورشید", "The Sun", "شادی، موفقیت و انرژی مثبت."),
    ("داوری", "Judgement", "بیداری، ارزیابی و تصمیم سرنوشت‌ساز."),
    ("دنیا", "The World", "تکمیل یک دوره، رسیدن به هدف."),
]
MINOR_SUITS = {
    "جام (Cups)": "احساسات، روابط و عشق",
    "پنتاکل (Pentacles)": "مال، کار و مسائل مادی",
    "شمشیر (Swords)": "فکر، چالش و تصمیم‌گیری",
    "چوبدستی (Wands)": "انرژی، خلاقیت و شور",
}
MINOR_RANKS = [
    "آس", "دو", "سه", "چهار", "پنج", "شش", "هفت", "هشت", "نه", "ده",
    "پیک (Page)", "شوالیه (Knight)", "ملکه (Queen)", "شاه (King)",
]


def build_full_tarot_deck():
    deck = [(f"{fa} ({en})", meaning) for fa, en, meaning in MAJOR_ARCANA]
    for suit, theme in MINOR_SUITS.items():
        for rank in MINOR_RANKS:
            deck.append((f"{rank} {suit}", f"مرتبط با {theme}."))
    return deck


TAROT_DECK_FULL = build_full_tarot_deck()

# ============================================================
# محتوای فال‌بک طولانی (وقتی Gemini در دسترس نیست)
# ============================================================
FAL_LIST = [
    "امروز روز خوبیه برای شروع یه کار جدید. انرژی‌های اطرافت مثبت‌ان و اگه دلت رو به دریا بزنی، "
    "نتیجه بهتر از چیزیه که فکرشو می‌کنی. فقط حواست باشه عجله نکنی و قدم‌به‌قدم پیش بری. 🌊",
    "یه خبر خوب از یه جای کاملاً غیرمنتظره بهت می‌رسه، شاید از طرف کسی که مدت‌ها ازش خبر نداشتی. "
    "این خبر می‌تونه مسیر چند روز آینده‌ت رو تغییر بده، پس ذهنت رو باز نگه دار. 📩",
    "امروز حواست به حرف‌هایی که می‌زنی باشه، یکی خیلی جدی داره گوش می‌ده و حرفات براش اهمیت داره. "
    "این یه فرصت خوبه که با صداقت و آرامش صحبت کنی، نه با عجله. 👂",
    "وقتشه یه قدم بزرگ برای هدفت برداری. ماه‌هاست که آماده می‌شی، الان بهترین زمان برای عمل کردنه، "
    "نه فکر کردن بیشتر. ترست رو کنار بذار و شروع کن. 🚀",
    "یه دوست قدیمی به یادت می‌افته و احتمالاً بهت پیام می‌ده. اگه زودتر از اون پیام بدی، "
    "این ارتباط دوباره جون می‌گیره و می‌تونه خیلی خوب پیش بره. 💬",
    "یه فرصت مالی خوب سر راهت قرار می‌گیره، ولی باید هوشیار باشی و با عجله تصمیم نگیری. "
    "قبل از هر قدمی، همه جوانب رو بررسی کن. 💰",
    "امروز روز آرامشه. لازم نیست همه‌چیز رو امروز حل کنی، به خودت اجازه بده کمی استراحت کنی "
    "و انرژی بگیری برای روزهای پرکارتر جلوتر. ☕",
    "یه تصمیم مهم پیش روته که می‌تونه مسیر آینده‌ت رو عوض کنه. با فکر باز تصمیم بگیر، "
    "نه احساسی و ناگهانی؛ مشورت با یه آدم مورد اعتماد هم کمکت می‌کنه. 🧠",
    "عشق تو هوا موج می‌زنه! چه مجرد باشی چه در رابطه، این روزها احساسات پررنگ‌تر از همیشه‌ان. "
    "چشمات رو باز نگه دار، ممکنه یه نفر همین نزدیکی‌ها منتظرت باشه. ❤️",
    "امروز شانس باهاته. یه ریسک حساب‌شده که مدت‌هاست بهش فکر می‌کنی رو امتحان کن؛ "
    "احتمال موفقیتش بیشتر از چیزیه که فکرشو می‌کنی. 🎲",
]

HAFEZ_VERSES = [
    "الا یا ایها الساقی ادر کاسا و ناولها / که عشق آسان نمود اول ولی افتاد مشکل‌ها",
    "بیا تا گل برافشانیم و می در ساغر اندازیم / فلک را سقف بشکافیم و طرحی نو دراندازیم",
    "دوش وقت سحر از غصه نجاتم دادند / وندر آن ظلمت شب آب حیاتم دادند",
    "یوسف گم‌گشته باز آید به کنعان غم مخور / کلبهٔ احزان شود روزی گلستان غم مخور",
    "اگر آن ترک شیرازی به دست آرد دل ما را / به خال هندویش بخشم سمرقند و بخارا را",
    "سال‌ها دل طلب جام جم از ما می‌کرد / وان چه خود داشت ز بیگانه تمنا می‌کرد",
    "صبا به لطف بگو آن غزال رعنا را / که سر به کوه و بیابان تو داده‌ای ما را",
    "بلبلی برگ گلی خوش‌رنگ در منقار داشت / وندر آن برگ و نوا خوش ناله‌های زار داشت",
]

# چند ضرب‌المثل اصیل فارسی (فرهنگ عامه، بدون مالکیت معنوی خاص)
PROVERBS_FA = [
    "کار نیکو کردن از پر کردن است؛ هر کاری با تمرین جا می‌افته.",
    "آدمی به فکر نیک، به گفتار نیک، به کردار نیک می‌رسه.",
    "تا نباشد چیزکی، مردم نگویند چیزها.",
    "آب رفته به جوی باز نمی‌گرده، پس قدر لحظه رو بدون.",
    "سنگ بزرگ علامت نزدن است.",
    "کبوتر با کبوتر، باز با باز؛ کند همجنس با همجنس پرواز.",
    "هر که بامش بیش، برفش بیشتر.",
    "دیر رسیدن بهتر از هرگز نرسیدنه.",
    "از کوزه همان برون تراود که در اوست.",
    "با یک گل بهار نمی‌شه؛ صبر و پشتکار کلیده.",
]

# چند جوک کوتاه بی‌آزار برای وقتی Gemini در دسترس نیست
JOKES_FALLBACK = [
    "یارو رفته دکتر می‌گه دکتر یادم میره... دکتر می‌گه از کِی؟ می‌گه چی از کِی؟ 😄",
    "به کامپیوترم گفتم رمزتو بگو، گفت: 404 not found! 🤖",
    "رفتم آرایشگاه گفتم مثل بازیگرا کوتاه کن، الان مثل صحنه فیلم ترسناکم! ✂️",
    "دیشب خواب دیدم پولدار شدم، صبح بیدار شدم دیدم فقط خوابم زیاد شده! 😂",
]


# ============================================================
# تولید محتوا (فال / تاروت / حافظ) با Gemini + منبع واقعی + fallback
# ============================================================
async def generate_fal(name: str) -> str:
    prompt = (
        f"تو یک فالگیر خلاق و باتجربه فارسی‌زبان هستی. یک فال روزانه کامل و نسبتاً مفصل "
        f"(حداقل ۴ تا ۶ جمله) برای «{name}» بنویس که موضوعات مختلف زندگی (عشق، کار، مالی، روابط) "
        f"رو در بر بگیره. لحنت گرم، امیدوارکننده و جذاب باشه. فقط متن فارسی فال رو بنویس، "
        f"بدون مقدمه یا توضیح اضافه، و در پایان یک یا دو ایموجی مناسب اضافه کن."
    )
    result = await ask_gemini(prompt, max_tokens=500)
    return result if result else random.choice(FAL_LIST)


def fetch_hafez_from_ganjoor():
    """دریافت بیت واقعی حافظ از گنجور (ganjoor.net) - منبع رسمی و معتبر متون فارسی."""
    try:
        r = _http_session.get(
            "https://api.ganjoor.net/api/ganjoor/poem/random",
            params={"poetId": 2},
            timeout=8,
        )
        if r.status_code == 200:
            data = r.json()
            title = data.get("title", "")
            verses = data.get("verses", [])
            if verses:
                lines = [v.get("text", "") for v in verses[:4] if v.get("text")]
                if lines:
                    text = "\n".join(lines)
                    return f"{text}\n\n📌 از غزلیات حافظ - «{title}»"
    except Exception as e:
        logger.warning(f"Ganjoor fetch failed: {e}")
    return None


async def generate_hafez() -> str:
    verse = await asyncio.to_thread(fetch_hafez_from_ganjoor)
    source_note = ""
    if not verse:
        verse = random.choice(HAFEZ_VERSES)
        source_note = " (از دیوان حافظ)"

    prompt = (
        f"این ابیاتی از حافظ است:\n«{verse}»\n\n"
        f"یک تفسیر نسبتاً کامل (۳ تا ۵ جمله) از معنی و پیام این ابیات، به زبان فارسی روان و امروزی بنویس. "
        f"توضیح بده این ابیات چه پیامی برای زندگی امروز ما دارن."
    )
    interpretation = await ask_gemini(prompt, max_tokens=350)

    if interpretation:
        return f"📖 {verse}{source_note}\n\n💫 تفسیر:\n{interpretation}"
    return f"📖 {verse}{source_note}"


async def generate_tarot() -> str:
    card, base_meaning = random.choice(TAROT_DECK_FULL)
    prompt = (
        f"کارت تاروت «{card}» انتخاب شده که معنی پایه‌اش این است: «{base_meaning}». "
        f"یک تفسیر کامل، گرم و شخصی (۴ تا ۶ جمله) بر همین اساس به زبان فارسی روان بنویس؛ "
        f"درباره عشق، کار و آینده نزدیک بر اساس این کارت بگو."
    )
    result = await ask_gemini(prompt, max_tokens=400)
    interpretation = result if result else (
        f"{base_meaning} این کارت نشونه‌ی مسیریه که پیش روته؛ بهش فکر کن و ببین چطور "
        f"با شرایط فعلی زندگیت ارتباط داره."
    )

    # --- تحلیل و جمع‌بندی نهایی (یک پیام کوتاه که خلاصه و توصیه عملی می‌ده) ---
    summary_prompt = (
        f"بر اساس این تفسیر کارت تاروت:\n«{interpretation}»\n\n"
        f"فقط در یک یا دو جمله کوتاه، یک «جمع‌بندی نهایی و توصیه عملی» به زبان فارسی روان بده؛ "
        f"یعنی شخص دقیقاً امروز چیکار کنه یا به چی توجه کنه. فقط همون جمله رو بنویس، بدون مقدمه."
    )
    summary = await ask_gemini(summary_prompt, max_tokens=120)
    if not summary:
        summary = "🔎 جمع‌بندی: به دلت گوش بده و امروز رو با آرامش و بدون عجله جلو برو."
    else:
        summary = f"🔎 جمع‌بندی و توصیه:\n{summary}"

    return f"🃏 کارت: {card}\n\n{interpretation}\n\n{summary}"


# ============================================================
# قیمت دلار و بیت‌کوین - چند منبع، اگه یکی خطا داد بعدی رو امتحان می‌کنه
# ============================================================
# ============================================================
# قیمت دلار و بیت‌کوین - چند منبع واقعی، اگه یکی خطا داد بعدی رو امتحان می‌کنه
# ============================================================


def fetch_usd_price():
    # منبع ۱: نوبیتکس - نرخ تتر/تومان (صرافی واقعی و فعال، نزدیک‌ترین معادل نرخ بازار آزاد)
    try:
        r = _http_session.get(
            "https://api.nobitex.ir/market/stats",
            params={"srcCurrency": "usdt", "dstCurrency": "rls"},
            timeout=7,
        )
        if r.status_code == 200:
            data = r.json()
            stats = data.get("stats", {}).get("usdt-rls", {})
            latest = stats.get("latest")
            if latest:
                toman = int(float(latest)) // 10
                if toman > 1000:  # عدد منطقی (جلوگیری از قیمت خراب/صفر)
                    return toman, "نوبیتکس (نرخ تتر)"
    except Exception as e:
        logger.warning(f"Nobitex USD fetch failed: {e}")

    # منبع ۲: TGJU - یکی از پرکاربردترین و معتبرترین سایت‌های قیمت ارز و طلای ایران
    # (این endpoint غیررسمی ولی بسیار پایدار و پراستفاده‌ست، خروجیش دلار به ریال با کاماست)
    try:
        r = _http_session.get("https://call1.tgju.org/ajax.json", timeout=7)
        if r.status_code == 200:
            data = r.json()
            price_raw = data.get("current", {}).get("price_dollar_rl", {}).get("p")
            if price_raw:
                clean = str(price_raw).replace(",", "").strip()
                rial = int(clean)
                toman = rial // 10
                if toman > 1000:
                    return toman, "TGJU"
    except Exception as e:
        logger.warning(f"TGJU USD fetch failed: {e}")

    return None, None


def fetch_btc_price():
    try:
        r = _http_session.get(
            "https://api.coingecko.com/api/v3/simple/price",
            params={"ids": "bitcoin", "vs_currencies": "usd"},
            timeout=7,
        )
        if r.status_code == 200:
            return r.json()["bitcoin"]["usd"], "CoinGecko"
    except Exception as e:
        logger.warning(f"CoinGecko BTC fetch failed: {e}")

    try:
        r = _http_session.get(
            "https://api.nobitex.ir/market/stats",
            params={"srcCurrency": "btc", "dstCurrency": "usdt"},
            timeout=7,
        )
        if r.status_code == 200:
            data = r.json()
            stats = data.get("stats", {}).get("btc-usdt", {})
            latest = stats.get("latest")
            if latest:
                return float(latest), "نوبیتکس"
    except Exception as e:
        logger.warning(f"Nobitex BTC fetch failed: {e}")

    try:
        r = _http_session.get("https://api.coincap.io/v2/assets/bitcoin", timeout=7)
        if r.status_code == 200:
            price = float(r.json()["data"]["priceUsd"])
            return price, "CoinCap"
    except Exception as e:
        logger.warning(f"CoinCap BTC fetch failed: {e}")

    return None, None


async def fetch_prices():
    now = datetime.now()
    if PRICE_CACHE["data"] and PRICE_CACHE["time"] and now - PRICE_CACHE["time"] < timedelta(seconds=CACHE_SECONDS):
        return PRICE_CACHE["data"]

    # هر دو منبع رو هم‌زمان (به‌جای پشت‌سرهم) توی ترد جدا می‌گیریم تا هم سریع‌تر باشه هم قفل نکنه
    (usd_toman, usd_source), (btc_usd, btc_source) = await asyncio.gather(
        asyncio.to_thread(fetch_usd_price),
        asyncio.to_thread(fetch_btc_price),
    )

    result = {
        "usd_toman": usd_toman, "usd_source": usd_source,
        "btc_usd": btc_usd, "btc_source": btc_source,
        "btc_toman": int(btc_usd * usd_toman) if (btc_usd and usd_toman) else None,
    }
    PRICE_CACHE["data"] = result
    PRICE_CACHE["time"] = now
    return result


# ============================================================
# حافظه کوتاه‌مدت گروه — برای مکالمه با زمینه، با پاک‌سازی خودکار هفتگی
# ============================================================
_memory_dirty = False  # به‌جای نوشتن روی دیسک در هر پیام، فقط فلگ می‌زنیم؛ یه جاب دوره‌ای ذخیره‌ش می‌کنه


def remember_message(chat_id, role: str, name: str, text: str):
    global _memory_dirty
    key = str(chat_id)
    entries = chat_memory.setdefault(key, [])
    entries.append({
        "role": role,
        "name": name,
        "text": text[:500],
        "time": datetime.now().isoformat(),
    })
    if len(entries) > MEMORY_MAX_PER_CHAT:
        del entries[: len(entries) - MEMORY_MAX_PER_CHAT]
    _memory_dirty = True  # ذخیره‌ی واقعی روی دیسک رو به flush_memory_job می‌سپاریم


async def flush_memory_job(context: ContextTypes.DEFAULT_TYPE):
    """هر ۳۰ ثانیه یک‌بار، فقط اگه چیزی عوض شده باشه، حافظه رو روی دیسک ذخیره می‌کنه.
    این کار به‌جای نوشتن فایل در هر پیام تکی، فشار I/O روی سرور رو خیلی کم می‌کنه."""
    global _memory_dirty
    if _memory_dirty:
        save_json_safe(MEMORY_FILE, chat_memory)
        _memory_dirty = False


def get_recent_context(chat_id, limit=MEMORY_CONTEXT_LIMIT):
    entries = chat_memory.get(str(chat_id), [])
    return entries[-limit:]


async def weekly_memory_cleanup(context: ContextTypes.DEFAULT_TYPE):
    """هر ۷ روز یک‌بار: پیام‌های قدیمی‌تر از ۷ روز رو، از قدیمی‌ترین به جدیدترین، از حافظه پاک می‌کنه."""
    cutoff = datetime.now() - timedelta(days=MEMORY_MAX_AGE_DAYS)
    changed = False
    for chat_id, entries in list(chat_memory.items()):
        kept = []
        for e in entries:  # entries از قبل به ترتیب قدیمی -> جدید هستن (append می‌شن)
            try:
                t = datetime.fromisoformat(e["time"])
            except Exception:
                changed = True
                continue
            if t >= cutoff:
                kept.append(e)
            else:
                changed = True
        chat_memory[chat_id] = kept
    if changed:
        global _memory_dirty
        save_json_safe(MEMORY_FILE, chat_memory)
        _memory_dirty = False
        logger.info("پاک‌سازی هفتگی حافظه گروه‌ها انجام شد.")


# ============================================================
# تشخیص و ترجمه شعر / متن غیرفارسی
# ============================================================
def looks_like_poem_or_foreign(text: str) -> bool:
    """تشخیص حدسی: متن چندخطی و عمدتاً غیرفارسیه (احتمالاً شعر/نقل‌قولی که نیاز به ترجمه داره)."""
    if text.startswith("/"):
        return False
    if len(text) < 12 or len(text) > 1500:
        return False
    if re.match(r"^https?://\S+$", text.strip()):
        return False
    lines = [l for l in text.split("\n") if l.strip()]
    if len(lines) < 2:
        return False
    persian_chars = len(re.findall(r"[آ-ی]", text))
    latin_chars = len(re.findall(r"[A-Za-z]", text))
    if persian_chars > 0 and persian_chars >= latin_chars:
        return False
    return latin_chars >= 8 or (persian_chars == 0 and len(text.strip()) >= 12)


async def translate_text(text: str) -> "str | None":
    prompt = (
        "متن زیر رو به فارسیِ روان، ساده و طبیعی ترجمه کن؛ ترجمه‌ی آزاد و قابل‌فهم بخواه، نه لغت‌به‌لغت. "
        "اگه شعر باشه، حال‌وهوای شاعرانه‌ش رو هم تا حد امکان حفظ کن. فقط ترجمه رو بنویس، بدون مقدمه:\n\n" + text
    )
    return await ask_gemini(prompt, max_tokens=600, temperature=0.7)


# ============================================================
# مکالمه هوشمند و بامزه با اعضای گروه
# ============================================================
BOT_PERSONALITY = (
    "تو یه ربات تلگرامی باحال، باهوش و حاضرجوابی که توی یه گروه دوستانه فعالیت می‌کنی. "
    "با اعضا و مخصوصاً ادمین‌های گروه مثل یه دوست صمیمی و واقعی حرف می‌زنی. "
    "خیلی مهمه که واقعاً منظور و حس پشت حرف طرف رو بفهمی و دقیقاً به همون جواب بدی، نه یه جواب کلی و الکی که به هر پیامی می‌شه داد. "
    "اگه شوخی کرد، باهاش بخند و شوخی رو ادامه بده؛ اگه جدی حرف زد یا سوال واقعی پرسید، جدی و دقیق جواب بده؛ "
    "اگه ناراحت یا عصبانی بود، متوجه باش و طبق حالش رفتار کن. "
    "گاهی شوخی و متلک سبک (بدون توهین واقعی) هم می‌ندازی. از ایموجی مناسب استفاده کن ولی زیاده‌روی نکن. "
    "جواب‌ها رو متناسب با پیام بده: اگه پیام ساده‌ست کوتاه جواب بده، اگه واقعاً نیاز به توضیح داره، کامل و دقیق توضیح بده."
)


async def generate_chat_reply(chat_id, user_name: str, message_text: str) -> str:
    entries = get_recent_context(chat_id)
    history_lines = [f"{'ربات' if e['role'] == 'bot' else e['name']}: {e['text']}" for e in entries]
    history_text = "\n".join(history_lines) if history_lines else "(هنوز مکالمه‌ای نبوده)"

    prompt = (
        f"{BOT_PERSONALITY}\n\n"
        f"چند پیام اخیر گروه (برای اینکه بفهمی بحث سر چیه و با زمینه‌ی مکالمه جواب بدی):\n{history_text}\n\n"
        f"حالا «{user_name}» این پیام رو مستقیم به تو گفته: «{message_text}»\n\n"
        f"اول توی ذهنت واقعاً بفهم منظورش چیه و چی می‌خواد بگه یا بپرسه، بعد دقیقاً بر همون اساس، "
        f"مثل یه دوست واقعی (نه یه ربات کلیشه‌ای) به زبان فارسی روان جواب بده. جواب باید مرتبط و خاصِ همین پیام باشه، "
        f"نه یه جواب عمومی که به هر پیامی می‌خوره."
    )
    result = await ask_gemini(prompt, max_tokens=350, temperature=0.9)
    if result:
        return result
    return random.choice([
        "هان؟ یه‌بار دیگه بگو 😄",
        "دارم فکر می‌کنم... یکم بعد جوابتو می‌دم 😅",
        "الان یکم سرم شلوغه، ولی حواسم بهته 😉",
    ])


# ============================================================
# منوی شیک (Inline Keyboard)
# ============================================================
def main_menu_keyboard():
    keyboard = [
        [InlineKeyboardButton("🔮 فال روزانه", callback_data="fal"),
         InlineKeyboardButton("🃏 تاروت", callback_data="tarot")],
        [InlineKeyboardButton("📖 فال حافظ", callback_data="hafez"),
         InlineKeyboardButton("🎯 شانس امروز", callback_data="shans")],
        [InlineKeyboardButton("💵 قیمت دلار", callback_data="dollar"),
         InlineKeyboardButton("₿ قیمت بیت‌کوین", callback_data="bitcoin")],
        [InlineKeyboardButton("😂 جوک", callback_data="joke"),
         InlineKeyboardButton("💬 ضرب‌المثل", callback_data="quote")],
        [InlineKeyboardButton("🐺 بازی گرگینه", callback_data="start_werewolf")],
        [InlineKeyboardButton("🤖 گفتگو با هوش مصنوعی", callback_data="gemini_chat")],
        [InlineKeyboardButton("📜 قوانین گروه", callback_data="rules"),
         InlineKeyboardButton("ℹ️ راهنما", callback_data="help")],
    ]
    return InlineKeyboardMarkup(keyboard)


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    text = (
        "✨ به ربات فال و سرگرمی خوش اومدی! ✨\n\n"
        "از دکمه‌های زیر استفاده کن یا از منوی دستورات (کنار جعبه پیام).\n"
        "این ربات همچنین به‌صورت خودکار پیام‌های نامناسب رو تشخیص می‌ده، شعرهای غیرفارسی رو ترجمه می‌کنه "
        "و اگه صداش کنی (با ریپلای یا کلمه «ربات») باهات گپ می‌زنه! 🤖"
    )
    await update.message.reply_text(text, reply_markup=main_menu_keyboard())


async def button_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    try:
        await query.answer()
    except Exception:
        pass

    data = query.data

    if data.startswith("rps_"):
        await handle_rps_choice(query, data)
        return

    if data == "start_werewolf":
        if query.message.chat.type == "private":
            await query.message.reply_text("🐺 این بازی فقط توی گروه قابل اجراست.")
        else:
            await ww_start_lobby(query.message.chat.id, query.from_user.id, context)
        return

    if data == "gemini_chat":
        # اول یه تست کوچیک می‌زنیم تا مطمئن بشیم Gemini الان واقعاً جواب می‌ده،
        # وگرنه به‌جای کرش یا سکوت، یه پیام روشن و درست به کاربر نشون می‌دیم.
        test = await ask_gemini("فقط بگو «سلام»", max_tokens=20)
        key = f"{query.message.chat_id}:{query.from_user.id}"
        if test:
            direct_chat_users.add(key)
            await query.message.reply_text(
                "🤖 وصل شدم! از همین الان هر پیامی بفرستی مستقیم باهات حرف می‌زنم، "
                "دیگه لازم نیست ریپلای بزنی یا کلمه «ربات» رو بگی.\n"
                "برای خروج از این حالت، دستور /stopchat رو بزن."
            )
        else:
            direct_chat_users.discard(key)
            await query.message.reply_text(
                "⚠️ الان امکان اتصال به هوش مصنوعی نیست (احتمالاً مشکل موقتی از سمت سرویس Gemini، "
                "مثل اتمام سهمیه یا نیاز به فعال‌سازی صورتحساب کلید). چند دقیقه دیگه دوباره امتحان کن؛ "
                "تا اون موقع بقیه بخش‌های ربات (فال، تاروت، قیمت‌ها و...) عادی کار می‌کنن."
            )
        return

    user_name = query.from_user.first_name or "دوست عزیز"

    try:
        if data == "fal":
            text = f"🔮 فال امروز {user_name}:\n\n{await generate_fal(user_name)}"
        elif data == "tarot":
            text = await generate_tarot()
        elif data == "hafez":
            text = await generate_hafez()
        elif data == "shans":
            text = f"🎯 شانس امروزت: {random.randint(1, 100)}٪"
        elif data == "dollar":
            p = await fetch_prices()
            text = (f"💵 قیمت دلار: {p['usd_toman']:,} تومان\n(منبع: {p['usd_source']})"
                    if p["usd_toman"] else "⚠️ فعلاً هیچ‌کدوم از منابع قیمت در دسترس نیستن، چند لحظه دیگه دوباره امتحان کن.")
        elif data == "bitcoin":
            p = await fetch_prices()
            if p["btc_usd"]:
                text = f"₿ قیمت بیت‌کوین: ${p['btc_usd']:,}\n(منبع: {p['btc_source']})"
                if p["btc_toman"]:
                    text += f"\nمعادل: {p['btc_toman']:,} تومان"
            else:
                text = "⚠️ فعلاً هیچ‌کدوم از منابع قیمت در دسترس نیستن، چند لحظه دیگه دوباره امتحان کن."
        elif data == "joke":
            joke_text = await ask_gemini("یه جوک کوتاه، بامزه و بی‌آزار فارسی بگو، بدون توهین یا سیاست. فقط متن جوک.", max_tokens=150)
            text = f"😂 {joke_text or random.choice(JOKES_FALLBACK)}"
        elif data == "quote":
            text = f"💬 {random.choice(PROVERBS_FA)}"
        elif data == "rules":
            text = (
                "📜 قوانین گروه:\n\n"
                "۱. احترام به همه اعضا الزامیه\n"
                "۲. استفاده از الفاظ رکیک ممنوعه (تشخیص خودکار)\n"
                "۳. تبلیغات بدون هماهنگی ادمین ممنوعه\n"
                "۴. اسپم و ارسال پی‌درپی پیام ممنوعه"
            )
        elif data == "help":
            text = (
                "ℹ️ راهنمای دستورات:\n\n"
                "🎉 سرگرمی: /fal /tarot /hafez /shans /joke /quote /compliment /roast /rps /coin /dice /love\n"
                "🐺 بازی گروهی: /gorgineh (شروع لابی گرگینه) /startgame /endgame /players\n"
                "💰 قیمت: /dollar /bitcoin /price\n"
                "🌐 ترجمه: /translate (روی پیام ریپلای کن)\n"
                "👥 گروه: /rules /report /id /stats /botstatus\n"
                "🛡️ ادمین: /mute /unmute /kick /ban /warn /pin /unpin /purge /addbad /removebad /listbad\n\n"
                "برای گپ زدن، فقط روی پیام‌های من ریپلای بزن، کلمه «ربات» رو توی پیامت بیار، "
                "یا از دکمه «🤖 گفتگو با هوش مصنوعی» بزن تا مستقیم و بدون هیچ‌کدوم از این‌ها باهام حرف بزنی "
                "(با /stopchat می‌تونی از این حالت خارج بشی) 😉"
            )
        else:
            text = "دستور نامشخص."
    except Exception as e:
        logger.error(f"خطا در button_handler: {e}")
        text = "⚠️ یه مشکل موقتی پیش اومد، لطفاً دوباره امتحان کن."

    try:
        await query.message.reply_text(text, reply_markup=main_menu_keyboard())
    except BadRequest as e:
        logger.warning(f"خطای ارسال پیام دکمه: {e}")
        await query.message.reply_text(text[:4000])


# ============================================================
# دستورات فال
# ============================================================
async def fal_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    name = update.effective_user.first_name or "دوست عزیز"
    await update.message.reply_text(f"🔮 فال امروز {name}:\n\n{await generate_fal(name)}")


async def tarot_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(await generate_tarot())


async def hafez_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(await generate_hafez())


async def shans_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(f"🎯 شانس امروزت: {random.randint(1, 100)}٪")


async def rules_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    text = (
        "📜 قوانین گروه:\n\n"
        "۱. احترام به همه اعضا الزامیه\n"
        "۲. استفاده از الفاظ رکیک ممنوعه (تشخیص خودکار)\n"
        "۳. تبلیغات بدون هماهنگی ادمین ممنوعه\n"
        "۴. اسپم و ارسال پی‌درپی پیام ممنوعه"
    )
    await update.message.reply_text(text)


async def dollar_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    p = await fetch_prices()
    text = (f"💵 قیمت دلار: {p['usd_toman']:,} تومان\n(منبع: {p['usd_source']})"
            if p["usd_toman"] else "⚠️ فعلاً هیچ‌کدوم از منابع قیمت در دسترس نیستن.")
    await update.message.reply_text(text)


async def bitcoin_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    p = await fetch_prices()
    if p["btc_usd"]:
        text = f"₿ قیمت بیت‌کوین: ${p['btc_usd']:,}\n(منبع: {p['btc_source']})"
        if p["btc_toman"]:
            text += f"\nمعادل: {p['btc_toman']:,} تومان"
    else:
        text = "⚠️ فعلاً هیچ‌کدوم از منابع قیمت در دسترس نیستن."
    await update.message.reply_text(text)


async def price_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    p = await fetch_prices()
    lines = ["📊 قیمت‌های لحظه‌ای:\n"]
    lines.append(f"💵 دلار: {p['usd_toman']:,} تومان ({p['usd_source']})" if p["usd_toman"] else "💵 دلار: نامشخص")
    lines.append(f"₿ بیت‌کوین: ${p['btc_usd']:,} ({p['btc_source']})" if p["btc_usd"] else "₿ بیت‌کوین: نامشخص")
    await update.message.reply_text("\n".join(lines))


async def id_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    chat = update.effective_chat
    text = f"👤 آیدی تو: {user.id}\n💬 آیدی این چت: {chat.id}"
    if update.message.reply_to_message:
        target = update.message.reply_to_message.from_user
        text += f"\n🎯 آیدی کاربر ریپلای‌شده: {target.id}"
    await update.message.reply_text(text)


# ============================================================
# دستورات سرگرمی جدید
# ============================================================
def get_target_user(update: Update):
    if update.message.reply_to_message:
        return update.message.reply_to_message.from_user
    return None


async def translate_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    reply = update.message.reply_to_message
    if not reply or not reply.text:
        await update.message.reply_text("روی پیام متنی که می‌خوای ترجمه بشه ریپلای بزن و بنویس /translate")
        return
    result = await translate_text(reply.text)
    await update.message.reply_text(f"🌐 ترجمه:\n\n{result}" if result else "⚠️ الان نشد ترجمه کنم، یکم بعد دوباره امتحان کن.")


async def joke_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    text = await ask_gemini("یه جوک کوتاه، بامزه و بی‌آزار فارسی بگو، بدون توهین یا سیاست. فقط متن جوک.", max_tokens=150)
    await update.message.reply_text(f"😂 {text or random.choice(JOKES_FALLBACK)}")


async def quote_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(f"💬 {random.choice(PROVERBS_FA)}")


async def compliment_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    target = get_target_user(update)
    name = target.first_name if target else update.effective_user.first_name
    prompt = f"یه تعریف بامزه، گرم و کمی اغراق‌آمیز (به شکل طنز دوستانه) از شخصی به نام «{name}» به فارسی بنویس. کوتاه و باحال."
    text = await ask_gemini(prompt, max_tokens=150) or f"{name} جان، همینکه هستی کافیه که روز آدم رو بسازه! ✨"
    await update.message.reply_text(text)


async def roast_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    target = get_target_user(update)
    if not target:
        await update.message.reply_text("روی پیام کسی که می‌خوای بهش متلک بامزه بندازی ریپلای بزن و بنویس /roast")
        return
    name = target.first_name
    prompt = (
        f"یه متلک بامزه، سبک و کاملاً دوستانه (بدون توهین واقعی، فحش یا حرف زننده) به شخصی به اسم «{name}» بگو، "
        f"مثل شوخی‌های معمول بین دوستا. فقط یک یا دو جمله."
    )
    text = await ask_gemini(prompt, max_tokens=120) or f"{name} جان، امروز حسابی سوژه شدی! 😄"
    await update.message.reply_text(text)


async def love_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    target = get_target_user(update)
    name1 = user.first_name
    name2 = target.first_name if target else (" ".join(context.args) if context.args else None)
    if not name2:
        await update.message.reply_text("یا روی پیام کسی ریپلای بزن، یا بنویس: /love اسم")
        return
    percent = sum(ord(c) for c in (name1 + name2)) % 101
    bar = "❤️" * (percent // 10) + "🖤" * (10 - percent // 10)
    await update.message.reply_text(f"💘 عشق‌سنج {name1} و {name2}:\n{bar}\n{percent}٪")


async def coin_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(f"🪙 نتیجه: {random.choice(['شیر', 'خط'])}")


async def dice_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(f"🎲 عدد تاس: {random.randint(1, 6)}")


RPS_EMOJI = {"rock": "🪨", "paper": "📄", "scissors": "✂️"}
RPS_FA = {"rock": "سنگ", "paper": "کاغذ", "scissors": "قیچی"}


def rps_outcome(user_choice, bot_choice):
    if user_choice == bot_choice:
        return "مساوی"
    beats = {"rock": "scissors", "paper": "rock", "scissors": "paper"}
    return "برد" if beats[user_choice] == bot_choice else "باخت"


async def rps_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    keyboard = [[
        InlineKeyboardButton("🪨 سنگ", callback_data="rps_rock"),
        InlineKeyboardButton("📄 کاغذ", callback_data="rps_paper"),
        InlineKeyboardButton("✂️ قیچی", callback_data="rps_scissors"),
    ]]
    await update.message.reply_text("یکی رو انتخاب کن:", reply_markup=InlineKeyboardMarkup(keyboard))


async def handle_rps_choice(query, data):
    user_choice = data.split("_", 1)[1]
    bot_choice = random.choice(list(RPS_EMOJI.keys()))
    outcome = rps_outcome(user_choice, bot_choice)
    outcome_fa = {"برد": "بردی! 🎉", "باخت": "باختی! 😅", "مساوی": "مساوی شدیم! 🤝"}[outcome]
    text = (
        f"تو: {RPS_EMOJI[user_choice]} {RPS_FA[user_choice]}\n"
        f"من: {RPS_EMOJI[bot_choice]} {RPS_FA[bot_choice]}\n\n{outcome_fa}"
    )
    await query.message.reply_text(text)


# ============================================================
# مدیریت لیست کلمات نامناسب توسط ادمین‌ها
# ============================================================
async def addbad_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ فقط ادمین‌های گروه می‌تونن کلمه اضافه کنن.")
        return
    if not context.args:
        await update.message.reply_text("استفاده: /addbad کلمه_موردنظر")
        return
    word = " ".join(context.args).strip().lower()
    target = BAD_WORDS_FA if re.search(r"[آ-ی]", word) else BAD_WORDS_EN
    if word not in target:
        target.append(word)
        save_json_safe(BAD_WORDS_FILE, {"fa": BAD_WORDS_FA, "en": BAD_WORDS_EN})
        await update.message.reply_text(f"✅ کلمه «{word}» به لیست اضافه شد.")
    else:
        await update.message.reply_text("این کلمه از قبل توی لیسته.")


async def removebad_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ فقط ادمین‌های گروه می‌تونن کلمه حذف کنن.")
        return
    if not context.args:
        await update.message.reply_text("استفاده: /removebad کلمه_موردنظر")
        return
    word = " ".join(context.args).strip().lower()
    removed = False
    if word in BAD_WORDS_FA:
        BAD_WORDS_FA.remove(word)
        removed = True
    if word in BAD_WORDS_EN:
        BAD_WORDS_EN.remove(word)
        removed = True
    if removed:
        save_json_safe(BAD_WORDS_FILE, {"fa": BAD_WORDS_FA, "en": BAD_WORDS_EN})
        await update.message.reply_text(f"✅ کلمه «{word}» از لیست حذف شد.")
    else:
        await update.message.reply_text("این کلمه توی لیست نبود.")


async def listbad_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ فقط ادمین‌های گروه می‌تونن ببینن.")
        return
    count = len(BAD_WORDS_FA) + len(BAD_WORDS_EN)
    await update.message.reply_text(f"📋 تعداد کلمات فیلترشده: {count}")


# ============================================================
# دستورات مدیریتی گروه (فقط ادمین)
# ============================================================
async def mute_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ فقط ادمین‌ها می‌تونن این کار رو بکنن.")
        return
    target = get_target_user(update)
    if not target:
        await update.message.reply_text("روی پیام فردی که می‌خوای سکوتش کنی ریپلای بزن و بنویس /mute")
        return
    try:
        await context.bot.restrict_chat_member(
            update.effective_chat.id, target.id,
            permissions=ChatPermissions(can_send_messages=False),
        )
        await update.message.reply_text(f"🔇 {target.first_name} تا اطلاع بعدی سکوت شد.")
    except TelegramError as e:
        await update.message.reply_text(f"⚠️ نشد: {e}\n\nاحتمالاً من توی این گروه ادمین نیستم یا دسترسی محدودسازی اعضا رو ندارم. با /botstatus وضعیتم رو چک کن.")


async def unmute_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ فقط ادمین‌ها می‌تونن این کار رو بکنن.")
        return
    target = get_target_user(update)
    if not target:
        await update.message.reply_text("روی پیام فردی که می‌خوای صداش رو باز کنی ریپلای بزن و بنویس /unmute")
        return
    try:
        await context.bot.restrict_chat_member(
            update.effective_chat.id, target.id,
            permissions=ChatPermissions(
                can_send_messages=True, can_send_audios=True, can_send_photos=True,
                can_send_videos=True, can_send_other_messages=True,
            ),
        )
        await update.message.reply_text(f"🔊 {target.first_name} دوباره می‌تونه پیام بده.")
    except TelegramError as e:
        await update.message.reply_text(f"⚠️ نشد: {e}")


async def kick_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ فقط ادمین‌ها می‌تونن این کار رو بکنن.")
        return
    target = get_target_user(update)
    if not target:
        await update.message.reply_text("روی پیام فردی که می‌خوای اخراجش کنی ریپلای بزن و بنویس /kick")
        return
    try:
        chat_id = update.effective_chat.id
        await context.bot.ban_chat_member(chat_id, target.id)
        await context.bot.unban_chat_member(chat_id, target.id)
        await update.message.reply_text(f"👢 {target.first_name} از گروه اخراج شد.")
    except TelegramError as e:
        await update.message.reply_text(f"⚠️ نشد: {e}")


async def ban_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ فقط ادمین‌ها می‌تونن این کار رو بکنن.")
        return
    target = get_target_user(update)
    if not target:
        await update.message.reply_text("روی پیام فردی که می‌خوای بنش کنی ریپلای بزن و بنویس /ban")
        return
    try:
        await context.bot.ban_chat_member(update.effective_chat.id, target.id)
        await update.message.reply_text(f"⛔ {target.first_name} برای همیشه بن شد.")
    except TelegramError as e:
        await update.message.reply_text(f"⚠️ نشد: {e}")


async def warn_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ فقط ادمین‌ها می‌تونن این کار رو بکنن.")
        return
    target = get_target_user(update)
    if not target:
        await update.message.reply_text("روی پیام فردی که می‌خوای اخطار بدی ریپلای بزن و بنویس /warn")
        return
    await apply_warn(update, context, target, reason="دستور دستی ادمین")


async def apply_warn(update, context, target_user, reason: str):
    chat_id = update.effective_chat.id
    key = f"{chat_id}:{target_user.id}"
    warns_data[key] = warns_data.get(key, 0) + 1
    save_json_safe(WARN_FILE, warns_data)
    count = warns_data[key]

    if count >= 3:
        try:
            await context.bot.restrict_chat_member(
                chat_id, target_user.id, permissions=ChatPermissions(can_send_messages=False),
            )
            warns_data[key] = 0
            save_json_safe(WARN_FILE, warns_data)
            await update.effective_chat.send_message(
                f"🔇 {target_user.first_name} به دلیل ۳ اخطار ({reason}) به‌صورت خودکار سکوت شد.\n"
                f"ادمین‌ها می‌تونن با /unmute (ریپلای روی پیامش) بازش کنن."
            )
        except TelegramError as e:
            logger.warning(f"خطای سکوت خودکار: {e}")
    else:
        await update.effective_chat.send_message(
            f"⚠️ اخطار {count}/۳ برای {target_user.first_name} ({reason})."
        )


async def pin_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ فقط ادمین‌ها می‌تونن این کار رو بکنن.")
        return
    if not update.message.reply_to_message:
        await update.message.reply_text("روی پیامی که می‌خوای پین کنی ریپلای بزن و بنویس /pin")
        return
    try:
        await context.bot.pin_chat_message(update.effective_chat.id, update.message.reply_to_message.message_id)
        await update.message.reply_text("📌 پیام پین شد.")
    except TelegramError as e:
        await update.message.reply_text(f"⚠️ نشد: {e}")


async def unpin_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ فقط ادمین‌ها می‌تونن این کار رو بکنن.")
        return
    try:
        await context.bot.unpin_chat_message(update.effective_chat.id)
        await update.message.reply_text("📌 پین پیام برداشته شد.")
    except TelegramError as e:
        await update.message.reply_text(f"⚠️ نشد: {e}")


async def purge_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ فقط ادمین‌ها می‌تونن این کار رو بکنن.")
        return
    if not context.args or not context.args[0].isdigit():
        await update.message.reply_text("استفاده: /purge تعداد  (مثلاً /purge 10 — حداکثر ۱۰۰)")
        return
    n = min(int(context.args[0]), 100)
    chat_id = update.effective_chat.id
    start_id = update.message.message_id
    deleted = 0
    for mid in range(start_id, start_id - n - 1, -1):
        try:
            await context.bot.delete_message(chat_id, mid)
            deleted += 1
        except TelegramError:
            continue
    await context.bot.send_message(chat_id, f"🧹 {deleted} پیام پاک شد.")


async def botstatus_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """نمایش دقیق دسترسی‌های فعلی ربات توی گروه - برای عیب‌یابی مشکل «ادمین نشدن»."""
    chat = update.effective_chat
    if chat.type == "private":
        await update.message.reply_text("این دستور فقط توی گروه معنی داره.")
        return
    try:
        member = await context.bot.get_chat_member(chat.id, context.bot.id)
        lines = [f"🤖 وضعیت من توی «{chat.title}»: {member.status}"]
        if member.status == "administrator":
            perms = {
                "حذف پیام": member.can_delete_messages,
                "محدود/سکوت کردن اعضا": member.can_restrict_members,
                "پین کردن پیام": member.can_pin_messages,
                "دعوت با لینک": member.can_invite_users,
            }
            for label, val in perms.items():
                lines.append(f"{'✅' if val else '❌'} {label}")
        else:
            lines.append(
                "\n⚠️ من الان ادمین این گروه نیستم، برای همین دستورات /mute /kick /ban /warn کار نمی‌کنن.\n\n"
                "برای ادمین کردنم (این کار رو فقط مالک یا یه ادمین دیگه‌ی گروه می‌تونه انجام بده، ربات نمی‌تونه خودشو ادمین کنه):\n"
                "۱. پروفایل گروه → Administrators → Add Admin\n"
                "۲. من رو از لیست اعضا انتخاب کن\n"
                "۳. حداقل «Delete messages» و «Ban/Restrict users» رو فعال کن\n"
                "۴. ذخیره کن"
            )
        await update.message.reply_text("\n".join(lines))
    except TelegramError as e:
        await update.message.reply_text(f"⚠️ نشد وضعیتم رو بگیرم: {e}")


# ============================================================
# فیلتر ناسزا + ضد اسپم + ترجمه شعر + مکالمه هوشمند روی پیام‌های گروه
# ============================================================
async def handle_group_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message or not update.message.text:
        return
    text = update.message.text
    user = update.effective_user
    chat = update.effective_chat

    if user.is_bot:
        return

    # --- ضد اسپم (flood control) ---
    now = time.time()
    times = user_message_times[f"{chat.id}:{user.id}"]
    times.append(now)
    if len(times) == FLOOD_LIMIT and (now - times[0]) < FLOOD_WINDOW:
        try:
            until = datetime.now() + timedelta(minutes=5)
            await context.bot.restrict_chat_member(
                chat.id, user.id,
                permissions=ChatPermissions(can_send_messages=False),
                until_date=until,
            )
            await update.message.reply_text(
                f"🚫 {user.first_name} به دلیل ارسال پیام زیاد و پشت‌سرهم، ۵ دقیقه سکوت شد."
            )
        except TelegramError as e:
            logger.warning(f"خطای ضد اسپم: {e}")
        return

    # --- فیلتر ناسزا ---
    if contains_bad_word(text):
        mention = mention_html(user)
        try:
            await update.message.reply_text(
                f"⚠️ {mention} لطفاً از الفاظ نامناسب استفاده نکن. این پیام گزارش شد.",
                parse_mode="HTML",
            )
        except Exception as e:
            logger.warning(f"خطای اخطار: {e}")

        try:
            admins = await context.bot.get_chat_administrators(chat.id)
            admin_mentions = [mention_html(a.user) for a in admins if not a.user.is_bot]
            if admin_mentions:
                await context.bot.send_message(
                    chat_id=chat.id,
                    text=f"🚨 توجه ادمین‌ها {' '.join(admin_mentions)}:\nکاربر {mention} از الفاظ نامناسب استفاده کرد.",
                    parse_mode="HTML",
                )
        except Exception as e:
            logger.warning(f"خطای اطلاع به ادمین: {e}")

        await apply_warn(update, context, user, reason="استفاده از الفاظ نامناسب")
        return

    # --- تشخیص و ترجمه شعر/متن غیرفارسی ---
    if looks_like_poem_or_foreign(text):
        translation = await translate_text(text)
        if translation:
            await update.message.reply_text(f"📜 ترجمه فارسی:\n\n{translation}")
        remember_message(chat.id, "user", user.first_name, text)
        return

    # --- ثبت پیام در حافظه کوتاه‌مدت گروه ---
    remember_message(chat.id, "user", user.first_name, text)

    # --- تشخیص اینکه آیا ربات مورد خطاب قرار گرفته ---
    triggered = False
    if f"{chat.id}:{user.id}" in direct_chat_users:
        triggered = True
    if update.message.reply_to_message and update.message.reply_to_message.from_user and \
            update.message.reply_to_message.from_user.id == context.bot.id:
        triggered = True
    bot_username = (context.bot.username or "").lower()
    if bot_username and f"@{bot_username}" in text.lower():
        triggered = True
    if any(w in text for w in TRIGGER_WORDS):
        triggered = True

    if triggered:
        reply = await generate_chat_reply(chat.id, user.first_name, text)
        await update.message.reply_text(reply)
        remember_message(chat.id, "bot", "ربات", reply)


async def stopchat_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    key = f"{update.effective_chat.id}:{update.effective_user.id}"
    direct_chat_users.discard(key)
    await update.message.reply_text("🔕 باشه، دیگه به پیام‌های عادیت جواب نمی‌دم مگه ریپلای بزنی یا بگی «ربات».")


# ============================================================
# گزارش به ادمین‌ها (/report روی یه پیام)
# ============================================================
async def report_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message.reply_to_message:
        await update.message.reply_text("روی پیامی که می‌خوای گزارش بدی ریپلای بزن و بنویس /report")
        return
    reporter = update.effective_user
    reported_msg = update.message.reply_to_message
    chat = update.effective_chat
    try:
        admins = await context.bot.get_chat_administrators(chat.id)
        admin_mentions = [mention_html(a.user) for a in admins if not a.user.is_bot]
        await context.bot.send_message(
            chat_id=chat.id,
            text=(
                f"🚨 گزارش جدید از طرف {mention_html(reporter)}:\n"
                f"پیام گزارش‌شده از: {mention_html(reported_msg.from_user)}\n\n"
                f"{' '.join(admin_mentions)}"
            ),
            parse_mode="HTML",
            reply_to_message_id=reported_msg.message_id,
        )
        await update.message.reply_text("✅ گزارش به ادمین‌ها ارسال شد.")
    except Exception as e:
        logger.warning(f"خطای گزارش: {e}")
        await update.message.reply_text("⚠️ گزارش ارسال نشد، دوباره امتحان کن.")


# ============================================================
# خوش‌آمدگویی و بدرقه اعضا
# ============================================================
async def welcome_new_member(update: Update, context: ContextTypes.DEFAULT_TYPE):
    for member in update.message.new_chat_members:
        if member.is_bot:
            continue
        text = (
            f"👋 سلام {member.first_name} عزیز، به گروه خوش اومدی!\n\n"
            f"لطفاً قوانین گروه رو با /rules ببین، و برای فال و سرگرمی /start رو بزن. خوش بگذره! 🎉"
        )
        await update.message.reply_text(text)


async def member_left(update: Update, context: ContextTypes.DEFAULT_TYPE):
    member = update.message.left_chat_member
    if member and not member.is_bot:
        await update.message.reply_text(f"👋 {member.first_name} از گروه رفت. به امید دیدار دوباره!")


# ============================================================
# آمار گروه
# ============================================================
async def stats_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat = update.effective_chat
    try:
        count = await context.bot.get_chat_member_count(chat.id)
        admins = await context.bot.get_chat_administrators(chat.id)
        text = (
            f"📊 آمار گروه «{chat.title}»:\n\n"
            f"👥 تعداد اعضا: {count}\n"
            f"👑 تعداد ادمین‌ها: {len(admins)}\n"
            f"📋 تعداد کلمات فیلترشده: {len(BAD_WORDS_FA) + len(BAD_WORDS_EN)}"
        )
    except Exception as e:
        text = f"⚠️ نشد آمار رو بگیرم: {e}"
    await update.message.reply_text(text)


# ============================================================
# منوی دستورات رسمی تلگرام
# ============================================================
async def set_commands(app):
    commands = [
        BotCommand("start", "منوی اصلی"),
        BotCommand("fal", "فال روزانه"),
        BotCommand("tarot", "کارت تاروت"),
        BotCommand("hafez", "فال حافظ"),
        BotCommand("shans", "درصد شانس امروز"),
        BotCommand("joke", "یه جوک بامزه"),
        BotCommand("quote", "یه ضرب‌المثل"),
        BotCommand("compliment", "تعریف بامزه از یه نفر (ریپلای کن)"),
        BotCommand("roast", "متلک بامزه و دوستانه (ریپلای کن)"),
        BotCommand("rps", "سنگ کاغذ قیچی"),
        BotCommand("coin", "شیر یا خط"),
        BotCommand("dice", "پرتاب تاس"),
        BotCommand("love", "عشق‌سنج شوخی"),
        BotCommand("gorgineh", "شروع بازی گروهی گرگینه"),
        BotCommand("startgame", "شروع زودهنگام گرگینه - فقط ادمین"),
        BotCommand("endgame", "لغو بازی گرگینه - فقط ادمین"),
        BotCommand("players", "لیست بازیکنان گرگینه"),
        BotCommand("translate", "ترجمه پیام به فارسی (ریپلای کن)"),
        BotCommand("dollar", "قیمت دلار"),
        BotCommand("bitcoin", "قیمت بیت‌کوین"),
        BotCommand("price", "قیمت دلار و بیت‌کوین"),
        BotCommand("rules", "قوانین گروه"),
        BotCommand("stats", "آمار گروه"),
        BotCommand("stopchat", "خروج از حالت گفتگوی مستقیم با هوش مصنوعی"),
        BotCommand("botstatus", "وضعیت و دسترسی‌های ربات توی گروه"),
        BotCommand("report", "گزارش پیام به ادمین (ریپلای کن)"),
        BotCommand("id", "دیدن آیدی عددی"),
        BotCommand("mute", "سکوت عضو - فقط ادمین (ریپلای کن)"),
        BotCommand("unmute", "باز کردن سکوت - فقط ادمین (ریپلای کن)"),
        BotCommand("kick", "اخراج عضو - فقط ادمین (ریپلای کن)"),
        BotCommand("ban", "بن عضو - فقط ادمین (ریپلای کن)"),
        BotCommand("warn", "اخطار به عضو - فقط ادمین (ریپلای کن)"),
        BotCommand("pin", "پین کردن پیام - فقط ادمین (ریپلای کن)"),
        BotCommand("unpin", "برداشتن پین - فقط ادمین"),
        BotCommand("purge", "پاک کردن N پیام اخیر - فقط ادمین"),
        BotCommand("addbad", "افزودن کلمه فیلتر - فقط ادمین"),
        BotCommand("removebad", "حذف کلمه فیلتر - فقط ادمین"),
        BotCommand("listbad", "تعداد کلمات فیلترشده - فقط ادمین"),
    ]
    await app.bot.set_my_commands(commands)


# ============================================================
# بازی گروهی گرگینه (روستا در خطر) - شبیه‌سازی مکانیک ربات معروف @WerewolfBot
# نقش‌ها: گرگ 🐺 / پیشگو 🔮 / دکتر 💉 / روستایی 👤
# جریان: لابی پیوستن -> پخش نقش خصوصی -> شب (اکشن خصوصی) -> روز (بحث + رأی) -> تکرار تا برد یکی از دو طرف
# ============================================================
WW_MIN_PLAYERS = 3
WW_MAX_PLAYERS = 16
WW_JOIN_SECONDS = 45
WW_NIGHT_SECONDS = 40
WW_DAY_DISCUSSION_SECONDS = 45
WW_VOTE_SECONDS = 30

WW_ROLE_FA = {"wolf": "🐺 گرگ", "seer": "🔮 پیشگو", "doctor": "💉 دکتر", "villager": "👤 روستایی"}
WW_ROLE_DESC = {
    "wolf": "هر شب همراه بقیه‌ی گرگ‌ها یه نفر رو انتخاب می‌کنی که کشته بشه. اگه تعداد گرگ‌ها به روستایی‌ها برسه، گرگ‌ها می‌برن. 🐺",
    "seer": "هر شب می‌تونی یه نفر رو چک کنی و بفهمی گرگه یا نه. کمک کن روستایی‌ها گرگ‌ها رو پیدا کنن. 🔮",
    "doctor": "هر شب می‌تونی یه نفر (حتی خودت) رو از کشته‌شدن نجات بدی. 💉",
    "villager": "قدرت خاصی نداری، ولی رأیت روزها مهمه؛ سعی کن با بحث گرگ‌ها رو لو بدی. 👤",
}

ww_games = {}        # chat_id -> WWGame
ww_player_game = {}  # user_id -> chat_id (بازی فعالی که توش عضوه، برای مسیریابی دکمه‌های خصوصی)


class WWPlayer:
    def __init__(self, user):
        self.id = user.id
        self.name = user.first_name or "بازیکن"
        self.role = None
        self.alive = True


class WWGame:
    def __init__(self, chat_id, host_id):
        self.chat_id = chat_id
        self.host_id = host_id
        self.state = "lobby"  # lobby, night, day_discuss, day_vote, ended
        self.players = {}
        self.round_no = 0
        self.night_kill_votes = {}
        self.seer_acted = False
        self.doctor_save = None
        self.last_victim_id = None
        self.last_saved = False
        self.day_votes = {}

    def alive_players(self):
        return [p for p in self.players.values() if p.alive]


def ww_assign_roles(player_ids):
    n = len(player_ids)
    wolves_count = max(1, n // 4)
    roles = ["wolf"] * wolves_count
    remaining = n - wolves_count
    if remaining >= 1 and n >= 5:
        roles.append("seer")
        remaining -= 1
    if remaining >= 1 and n >= 6:
        roles.append("doctor")
        remaining -= 1
    roles += ["villager"] * remaining
    random.shuffle(roles)
    return dict(zip(player_ids, roles))


def ww_check_win(game: "WWGame"):
    alive = game.alive_players()
    wolves = [p for p in alive if p.role == "wolf"]
    others = [p for p in alive if p.role != "wolf"]
    if len(wolves) == 0:
        return "village"
    if len(wolves) >= len(others):
        return "wolves"
    return None


def ww_cleanup_game(chat_id):
    game = ww_games.pop(chat_id, None)
    if game:
        for uid in list(game.players.keys()):
            if ww_player_game.get(uid) == chat_id:
                ww_player_game.pop(uid, None)


async def ww_start_lobby(chat_id, host_id, context: ContextTypes.DEFAULT_TYPE):
    if chat_id in ww_games and ww_games[chat_id].state != "ended":
        await context.bot.send_message(chat_id, "🐺 یه بازی از قبل توی این گروه در جریانه یا لابیش بازه.")
        return
    game = WWGame(chat_id, host_id)
    ww_games[chat_id] = game
    kb = [[InlineKeyboardButton("🐺 پیوستن به بازی", callback_data="ww_join")]]
    await context.bot.send_message(
        chat_id,
        (
            "🐺 بازی گرگینه (روستا در خطر) شروع شد!\n"
            f"حداقل {WW_MIN_PLAYERS} و حداکثر {WW_MAX_PLAYERS} نفر می‌تونن بازی کنن.\n"
            f"برای پیوستن دکمه‌ی زیر رو بزن، {WW_JOIN_SECONDS} ثانیه وقت داری.\n\n"
            "⚠️ حتماً قبلش یه‌بار توی خصوصی به من پیام بده (/start)، وگرنه نمی‌تونم نقشتو برات بفرستم.\n"
            "ادمین می‌تونه با /startgame زودتر شروع کنه یا با /endgame لغوش کنه."
        ),
        reply_markup=InlineKeyboardMarkup(kb),
    )
    context.application.create_task(ww_lobby_countdown(chat_id, context))


async def ww_lobby_countdown(chat_id, context: ContextTypes.DEFAULT_TYPE):
    await asyncio.sleep(WW_JOIN_SECONDS)
    game = ww_games.get(chat_id)
    if game and game.state == "lobby":
        await ww_try_start_game(chat_id, context)


async def ww_try_start_game(chat_id, context: ContextTypes.DEFAULT_TYPE):
    game = ww_games.get(chat_id)
    if not game or game.state != "lobby":
        return
    if len(game.players) < WW_MIN_PLAYERS:
        await context.bot.send_message(chat_id, f"❌ تعداد بازیکن‌ها کافی نبود (حداقل {WW_MIN_PLAYERS} نفر لازمه). بازی لغو شد.")
        ww_cleanup_game(chat_id)
        return

    roles = ww_assign_roles(list(game.players.keys()))
    for uid, role in roles.items():
        game.players[uid].role = role

    lines = ["🎭 نقش‌ها پخش شد! هر کس نقشش رو توی خصوصی می‌بینه.\n\n👥 بازیکنان:"]
    for p in game.players.values():
        lines.append(f"• {p.name}")
    await context.bot.send_message(chat_id, "\n".join(lines))

    for p in game.players.values():
        try:
            await context.bot.send_message(
                p.id, f"🎭 نقش تو توی این بازی: {WW_ROLE_FA[p.role]}\n\n{WW_ROLE_DESC[p.role]}"
            )
        except Forbidden:
            await context.bot.send_message(
                chat_id,
                f"⚠️ {p.name} عزیز، نتونستم نقشتو خصوصی بفرستم؛ اول به من پیام بده (/start) و دفعه بعد دوباره بازی کن.",
            )

    game.state = "night"
    context.application.create_task(ww_game_loop(chat_id, context))


async def ww_game_loop(chat_id, context: ContextTypes.DEFAULT_TYPE):
    game = ww_games[chat_id]
    try:
        while True:
            await ww_run_night(chat_id, context)
            winner = ww_check_win(game)
            if winner:
                await ww_announce_winner(chat_id, context, winner)
                break
            winner = await ww_run_day(chat_id, context)
            if winner:
                await ww_announce_winner(chat_id, context, winner)
                break
    except Exception as e:
        logger.error(f"خطا توی حلقه بازی گرگینه: {e}")
        await context.bot.send_message(chat_id, "⚠️ یه مشکل غیرمنتظره توی بازی پیش اومد و بازی متوقف شد.")
    finally:
        ww_cleanup_game(chat_id)


async def ww_run_night(chat_id, context: ContextTypes.DEFAULT_TYPE):
    game = ww_games[chat_id]
    game.state = "night"
    game.round_no += 1
    game.night_kill_votes = {}
    game.seer_acted = False
    game.doctor_save = None

    await context.bot.send_message(chat_id, f"🌙 شب {game.round_no} فرا رسید. همه بخوابید... نقش‌های خاص، به خصوصی من مراجعه کنید.")

    alive = game.alive_players()
    wolves = [p for p in alive if p.role == "wolf"]
    wolf_targets = [p for p in alive if p.role != "wolf"]

    for w in wolves:
        kb = [[InlineKeyboardButton(p.name, callback_data=f"ww_kill_{p.id}")] for p in wolf_targets]
        try:
            await context.bot.send_message(w.id, "🐺 امشب کی رو می‌کشید؟", reply_markup=InlineKeyboardMarkup(kb))
        except Forbidden:
            await context.bot.send_message(chat_id, f"⚠️ نتونستم به {w.name} پیام خصوصی بدم.")

    seer = next((p for p in alive if p.role == "seer"), None)
    if seer:
        targets = [p for p in alive if p.id != seer.id]
        kb = [[InlineKeyboardButton(p.name, callback_data=f"ww_seer_{p.id}")] for p in targets]
        try:
            await context.bot.send_message(seer.id, "🔮 کی رو می‌خوای چک کنی؟", reply_markup=InlineKeyboardMarkup(kb))
        except Forbidden:
            await context.bot.send_message(chat_id, f"⚠️ نتونستم به {seer.name} پیام خصوصی بدم.")

    doctor = next((p for p in alive if p.role == "doctor"), None)
    if doctor:
        kb = [[InlineKeyboardButton(p.name, callback_data=f"ww_save_{p.id}")] for p in alive]
        try:
            await context.bot.send_message(doctor.id, "💉 امشب کی رو نجات می‌دی؟", reply_markup=InlineKeyboardMarkup(kb))
        except Forbidden:
            await context.bot.send_message(chat_id, f"⚠️ نتونستم به {doctor.name} پیام خصوصی بدم.")

    waited = 0
    while waited < WW_NIGHT_SECONDS:
        await asyncio.sleep(2)
        waited += 2
        wolves_done = all(w.id in game.night_kill_votes for w in wolves) if wolves else True
        seer_done = (seer is None) or game.seer_acted
        doctor_done = (doctor is None) or (game.doctor_save is not None)
        if wolves_done and seer_done and doctor_done:
            break

    ww_resolve_night(game)


def ww_resolve_night(game: "WWGame"):
    votes = list(game.night_kill_votes.values())
    victim_id = None
    if votes:
        tally = {}
        for v in votes:
            tally[v] = tally.get(v, 0) + 1
        top_count = max(tally.values())
        top = [k for k, c in tally.items() if c == top_count]
        victim_id = random.choice(top)
    game.last_victim_id = victim_id
    game.last_saved = victim_id is not None and victim_id == game.doctor_save


async def ww_run_day(chat_id, context: ContextTypes.DEFAULT_TYPE):
    game = ww_games[chat_id]
    game.state = "day_discuss"

    victim_id = game.last_victim_id
    if victim_id and not game.last_saved:
        victim = game.players[victim_id]
        victim.alive = False
        await context.bot.send_message(
            chat_id, f"☀️ صبح شد... متأسفانه {victim.name} ({WW_ROLE_FA[victim.role]}) دیشب کشته شد. 💀"
        )
    elif victim_id and game.last_saved:
        await context.bot.send_message(chat_id, "☀️ صبح شد... دیشب یه نفر هدف گرگ‌ها بود ولی دکتر نجاتش داد! 🎉")
    else:
        await context.bot.send_message(chat_id, "☀️ صبح شد... دیشب اتفاق خاصی نیفتاد.")

    winner = ww_check_win(game)
    if winner:
        return winner

    await context.bot.send_message(chat_id, f"💬 {WW_DAY_DISCUSSION_SECONDS} ثانیه وقت دارید صحبت کنید و گرگ‌ها رو پیدا کنید...")
    await asyncio.sleep(WW_DAY_DISCUSSION_SECONDS)

    game.state = "day_vote"
    game.day_votes = {}
    alive = game.alive_players()
    kb = [[InlineKeyboardButton(p.name, callback_data=f"ww_vote_{p.id}")] for p in alive]
    await context.bot.send_message(chat_id, "🗳️ رأی‌گیری! کی رو می‌خواید اعدام کنید؟", reply_markup=InlineKeyboardMarkup(kb))

    waited = 0
    while waited < WW_VOTE_SECONDS:
        await asyncio.sleep(2)
        waited += 2
        if len(game.day_votes) >= len(alive):
            break

    text = ww_resolve_vote(game)
    await context.bot.send_message(chat_id, text)
    return ww_check_win(game)


def ww_resolve_vote(game: "WWGame") -> str:
    votes = list(game.day_votes.values())
    if not votes:
        return "🤷 هیچ‌کس رأی نداد، امروز کسی اعدام نشد."
    tally = {}
    for v in votes:
        tally[v] = tally.get(v, 0) + 1
    top_count = max(tally.values())
    top = [k for k, c in tally.items() if c == top_count]
    if len(top) > 1:
        return "⚖️ رأی‌ها مساوی شد، امروز کسی اعدام نشد."
    target_id = top[0]
    target = game.players[target_id]
    target.alive = False
    return f"⚖️ رأی گروه: {target.name} اعدام شد. نقشش {WW_ROLE_FA[target.role]} بود!"


async def ww_announce_winner(chat_id, context: ContextTypes.DEFAULT_TYPE, winner: str):
    game = ww_games[chat_id]
    reveal = "\n".join(f"• {p.name}: {WW_ROLE_FA[p.role]}" for p in game.players.values())
    text = "🎉 روستایی‌ها بردن و همه‌ی گرگ‌ها رو پیدا کردن!" if winner == "village" else "🐺 گرگ‌ها بردن و روستا رو تصرف کردن!"
    await context.bot.send_message(chat_id, f"{text}\n\n🎭 نقش همه:\n{reveal}")


async def gorgineh_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat = update.effective_chat
    if chat.type == "private":
        await update.message.reply_text("🐺 این بازی فقط توی گروه قابل اجراست.")
        return
    await ww_start_lobby(chat.id, update.effective_user.id, context)


async def startgame_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ فقط ادمین می‌تونه زودتر بازی رو شروع کنه.")
        return
    chat_id = update.effective_chat.id
    game = ww_games.get(chat_id)
    if not game or game.state != "lobby":
        await update.message.reply_text("لابی‌ای برای شروع نیست. اول با /gorgineh یکی بساز.")
        return
    await ww_try_start_game(chat_id, context)


async def endgame_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ فقط ادمین می‌تونه بازی رو لغو کنه.")
        return
    chat_id = update.effective_chat.id
    if chat_id in ww_games:
        ww_cleanup_game(chat_id)
        await update.message.reply_text("🛑 بازی گرگینه لغو شد.")
    else:
        await update.message.reply_text("بازی‌ای در جریان نیست.")


async def players_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.effective_chat.id
    game = ww_games.get(chat_id)
    if not game:
        await update.message.reply_text("بازی‌ای در جریان نیست.")
        return
    lines = [f"👥 بازیکنان ({len(game.players)} نفر):"]
    for p in game.players.values():
        lines.append(f"{'🟢' if p.alive else '💀'} {p.name}")
    await update.message.reply_text("\n".join(lines))


async def ww_button_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    try:
        await query.answer()
    except Exception:
        pass

    data = query.data
    user = query.from_user

    if data == "ww_join":
        chat_id = query.message.chat_id
        game = ww_games.get(chat_id)
        if not game or game.state != "lobby":
            await query.message.reply_text("لابی‌ای برای پیوستن نیست.")
            return
        if user.id in game.players:
            await query.message.reply_text(f"{user.first_name} جان، تو از قبل عضو بازی هستی!")
            return
        if len(game.players) >= WW_MAX_PLAYERS:
            await query.message.reply_text("ظرفیت بازی پره!")
            return
        game.players[user.id] = WWPlayer(user)
        ww_player_game[user.id] = chat_id
        await context.bot.send_message(chat_id, f"✅ {user.first_name} به بازی پیوست. ({len(game.players)} نفر)")
        return

    chat_id = ww_player_game.get(user.id)
    game = ww_games.get(chat_id) if chat_id else None
    if not game:
        await query.message.reply_text("این بازی دیگه فعال نیست.")
        return

    try:
        if data.startswith("ww_kill_"):
            target_id = int(data.split("_")[2])
            game.night_kill_votes[user.id] = target_id
            await query.message.reply_text(f"✅ رأیت ثبت شد: {game.players[target_id].name}")
        elif data.startswith("ww_seer_"):
            target_id = int(data.split("_")[2])
            target = game.players[target_id]
            game.seer_acted = True
            await query.message.reply_text(f"🔮 نتیجه: {target.name} {'گرگه! 🐺' if target.role == 'wolf' else 'گرگ نیست. ✅'}")
        elif data.startswith("ww_save_"):
            target_id = int(data.split("_")[2])
            game.doctor_save = target_id
            await query.message.reply_text(f"✅ ثبت شد: امشب {game.players[target_id].name} رو نجات می‌دی.")
        elif data.startswith("ww_vote_"):
            target_id = int(data.split("_")[2])
            game.day_votes[user.id] = target_id
            await query.message.reply_text("🗳️ رأیت ثبت شد.")
    except (KeyError, IndexError, ValueError) as e:
        logger.warning(f"خطای دکمه گرگینه: {e}")
        await query.message.reply_text("⚠️ یه مشکل موقتی پیش اومد.")


# ============================================================
# مدیریت خطای کلی (تا ربات هیچ‌وقت کرش نکنه)
# ============================================================
async def error_handler(update, context: ContextTypes.DEFAULT_TYPE):
    logger.error("خطای پیش‌بینی‌نشده:\n" + "".join(traceback.format_exception(type(context.error), context.error, context.error.__traceback__)))


def main():
    if not BOT_TOKEN:
        raise SystemExit("متغیر محیطی BOT_TOKEN تنظیم نشده. با export BOT_TOKEN=... مقداردهیش کن.")
    if not GEMINI_API_KEY:
        logger.warning("GEMINI_API_KEY تنظیم نشده؛ ربات فقط با محتوای fallback ثابت کار می‌کنه (بدون هوش مصنوعی).")

    app = ApplicationBuilder().token(BOT_TOKEN).build()

    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("fal", fal_cmd))
    app.add_handler(CommandHandler("tarot", tarot_cmd))
    app.add_handler(CommandHandler("hafez", hafez_cmd))
    app.add_handler(CommandHandler("shans", shans_cmd))
    app.add_handler(CommandHandler("rules", rules_cmd))
    app.add_handler(CommandHandler("dollar", dollar_cmd))
    app.add_handler(CommandHandler("bitcoin", bitcoin_cmd))
    app.add_handler(CommandHandler("price", price_cmd))
    app.add_handler(CommandHandler("id", id_cmd))
    app.add_handler(CommandHandler("stats", stats_cmd))
    app.add_handler(CommandHandler("report", report_cmd))
    app.add_handler(CommandHandler("stopchat", stopchat_cmd))
    app.add_handler(CommandHandler("botstatus", botstatus_cmd))

    app.add_handler(CommandHandler("translate", translate_cmd))
    app.add_handler(CommandHandler("joke", joke_cmd))
    app.add_handler(CommandHandler("quote", quote_cmd))
    app.add_handler(CommandHandler("compliment", compliment_cmd))
    app.add_handler(CommandHandler("roast", roast_cmd))
    app.add_handler(CommandHandler("rps", rps_cmd))
    app.add_handler(CommandHandler("coin", coin_cmd))
    app.add_handler(CommandHandler("dice", dice_cmd))
    app.add_handler(CommandHandler("love", love_cmd))

    # --- بازی گرگینه ---
    app.add_handler(CommandHandler("gorgineh", gorgineh_cmd))
    app.add_handler(CommandHandler("startgame", startgame_cmd))
    app.add_handler(CommandHandler("endgame", endgame_cmd))
    app.add_handler(CommandHandler("players", players_cmd))
    app.add_handler(CallbackQueryHandler(ww_button_handler, pattern=r"^ww_"))

    app.add_handler(CommandHandler("addbad", addbad_cmd))
    app.add_handler(CommandHandler("removebad", removebad_cmd))
    app.add_handler(CommandHandler("listbad", listbad_cmd))

    app.add_handler(CommandHandler("mute", mute_cmd))
    app.add_handler(CommandHandler("unmute", unmute_cmd))
    app.add_handler(CommandHandler("kick", kick_cmd))
    app.add_handler(CommandHandler("ban", ban_cmd))
    app.add_handler(CommandHandler("warn", warn_cmd))
    app.add_handler(CommandHandler("pin", pin_cmd))
    app.add_handler(CommandHandler("unpin", unpin_cmd))
    app.add_handler(CommandHandler("purge", purge_cmd))

    app.add_handler(CallbackQueryHandler(button_handler))
    app.add_handler(MessageHandler(filters.StatusUpdate.NEW_CHAT_MEMBERS, welcome_new_member))
    app.add_handler(MessageHandler(filters.StatusUpdate.LEFT_CHAT_MEMBER, member_left))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_group_text))

    app.add_error_handler(error_handler)
    app.post_init = set_commands

    if app.job_queue:
        app.job_queue.run_repeating(weekly_memory_cleanup, interval=timedelta(days=MEMORY_MAX_AGE_DAYS), first=60)
        app.job_queue.run_repeating(flush_memory_job, interval=30, first=30)
    else:
        logger.warning('JobQueue نصب نیست؛ برای پاک‌سازی خودکار هفتگی حافظه، pip install "python-telegram-bot[job-queue]" رو بزن.')

    print("✅ ربات روشن شد و در حال اجراست...")
    app.run_polling(drop_pending_updates=True)


if __name__ == "__main__":
    main()
