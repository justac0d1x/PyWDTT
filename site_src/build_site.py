import ast, base64, hashlib, io, json, os, re, shutil, sys
from string import Template
from PIL import Image

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
ASSETS = os.path.join(HERE, "assets")
SRC_PYW = os.path.join(ROOT, "pyWDTT.pyw")
SRC_ICO = os.path.join(ROOT, "pyWDTT.ico")
OUT = os.path.join(ROOT, "site")

os.makedirs(OUT, exist_ok=True)
data = open(SRC_PYW, "rb").read()
sha = hashlib.sha256(data).hexdigest()
size_mb = len(data) / 1048576
text = data.decode("utf-8")
VERSION = re.search(r"^VERSION = (.+)$", text, re.M).group(1).strip().strip("\"'")


def b64(path, mime):
    return "data:%s;base64,%s" % (mime, base64.b64encode(open(path, "rb").read()).decode())


icon = Image.open(os.path.join(ASSETS, "icon-256.webp")).convert("RGBA")
buf = io.BytesIO()
icon.resize((128, 128), Image.LANCZOS).save(buf, "PNG", optimize=True)
favicon = "data:image/png;base64," + base64.b64encode(buf.getvalue()).decode()

# облегчённая сборка: тот же код без вшитых колёс
SRC_LITE = os.path.join(ROOT, "pyWDTT-universal.py")
if not os.path.exists(SRC_LITE):
    import subprocess
    subprocess.run([sys.executable, os.path.join(ROOT, "build_lite.py")], check=True,
                   cwd=ROOT)
lite = open(SRC_LITE, "rb").read()
lite_sha = hashlib.sha256(lite).hexdigest()

# интерфейс приложения (HTML_INTERFACE) — встраиваем прямо в страницу и кладём рядом отдельной копией
app_html = None
for node in ast.parse(text).body:
    if isinstance(node, ast.Assign) and getattr(node.targets[0], "id", "") == "HTML_INTERFACE":
        app_html = ast.literal_eval(node.value)
        break
assert app_html and "pyWDTT" in app_html
open(os.path.join(OUT, "demo.html"), "w", encoding="utf-8").write(app_html)

# JSON-строка для <script>: экранируем "</", чтобы не закрыть тег раньше времени
demo_js = json.dumps(app_html, ensure_ascii=False).replace("</", "<\\/")

tpl = Template(open(os.path.join(HERE, "template.html"), encoding="utf-8").read())
html = tpl.safe_substitute(
    FONTS=open(os.path.join(ASSETS, "fonts.css"), encoding="utf-8").read(),
    FAVICON=favicon,
    ICON64=b64(os.path.join(ASSETS, "icon-64.webp"), "image/webp"),
    DEMO_HTML=demo_js,
    LITE_SIZE="%.2f МБ" % (len(lite) / 1048576),
    LITE_SHA256=lite_sha,
    VERSION=VERSION,
    SIZE="%.1f МБ" % size_mb,
    SHA256=sha,
)
open(os.path.join(OUT, "index.html"), "w", encoding="utf-8").write(html)
shutil.copy(SRC_PYW, os.path.join(OUT, "pyWDTT.pyw"))
shutil.copy(SRC_ICO, os.path.join(OUT, "pyWDTT.ico"))
shutil.copy(SRC_LITE, os.path.join(OUT, "pyWDTT-universal.py"))
open(os.path.join(OUT, ".nojekyll"), "w").write("")

print("версия %s | pyWDTT.pyw %s… | universal %s… | index.html %.0f КБ"
      % (VERSION, sha[:12], lite_sha[:12], os.path.getsize(os.path.join(OUT, "index.html")) / 1024))
