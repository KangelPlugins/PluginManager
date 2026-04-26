import os
import json
import re
from android.content import Intent
from android.net import Uri
from android_utils import log as _android_log, run_on_ui_thread
from client_utils import get_last_fragment, get_messages_controller
from hook_utils import get_private_field
from java.util import Locale


def _get_loading_html():
    try:
        from org.telegram.ui.ActionBar import Theme
        color_int = Theme.getColor(Theme.key_windowBackgroundWhiteBlueText)
        accent_color = "%06X" % (int(color_int) & 0xFFFFFF)
    except Exception:
        accent_color = "4F378B"
    
    return f"""
<!DOCTYPE html>
<html lang="ru">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <style>
        body {{
            display: flex;
            justify-content: center;
            align-items: center;
            margin: 0;
            height: 100vh;
            background: transparent;
            overflow: hidden;
        }}
        .svg-canvas {{
            width: 90px;
            height: 90px;
            overflow: visible;
        }}
        .expressive-snap {{
            transform-origin: 60px 60px;
            animation: snap-rotate 6s infinite;
        }}
        @keyframes snap-rotate {{
            0%   {{ transform: rotate(0deg); animation-timing-function: ease-out; }}
            12%  {{ transform: rotate(15deg); animation-timing-function: ease-in-out; }}
            15%  {{ transform: rotate(5deg); animation-timing-function: cubic-bezier(0.8, 0.0, 0.2, 1); }}
            25%  {{ transform: rotate(135deg); animation-timing-function: linear; }}
            25%  {{ transform: rotate(135deg); animation-timing-function: ease-out; }}
            37%  {{ transform: rotate(150deg); animation-timing-function: ease-in-out; }}
            40%  {{ transform: rotate(140deg); animation-timing-function: cubic-bezier(0.8, 0.0, 0.2, 1); }}
            50%  {{ transform: rotate(270deg); animation-timing-function: linear; }}
            50%  {{ transform: rotate(270deg); animation-timing-function: ease-out; }}
            62%  {{ transform: rotate(285deg); animation-timing-function: ease-in-out; }}
            65%  {{ transform: rotate(275deg); animation-timing-function: cubic-bezier(0.8, 0.0, 0.2, 1); }}
            75%  {{ transform: rotate(405deg); animation-timing-function: linear; }}
            75%  {{ transform: rotate(405deg); animation-timing-function: ease-out; }}
            87%  {{ transform: rotate(420deg); animation-timing-function: ease-in-out; }}
            90%  {{ transform: rotate(410deg); animation-timing-function: cubic-bezier(0.8, 0.0, 0.2, 1); }}
            100% {{ transform: rotate(540deg); animation-timing-function: linear; }}
        }}
    </style>
</head>
<body>
    <svg class="svg-canvas" viewBox="0 0 120 120">
        <g class="expressive-snap">
            <path class="morph-path" fill="#{accent_color}">
                <animate class="morph-anim" attributeName="d" dur="6s" repeatCount="indefinite" calcMode="spline" />
            </path>
        </g>
    </svg>
    <script>
        document.addEventListener('DOMContentLoaded', () => {{
            function generateGeometricPath(type, centerX = 60, centerY = 60) {{
                const numPoints = 120;
                const angleStep = (Math.PI * 2) / numPoints;
                let d = "";
                for (let i = 0; i < numPoints; i++) {{
                    const angle = i * angleStep;
                    let a = ((angle % (Math.PI * 2)) + Math.PI * 2) % (Math.PI * 2);
                    let r = 0;
                    if (type === 'flower') {{
                        r = 44 + 4 * Math.cos(10 * a);
                    }}
                    else if (type === 'blob') {{
                        const S = 40;
                        const R = 16;
                        let oct = a % (Math.PI / 2);
                        if (oct > Math.PI / 4) oct = Math.PI / 2 - oct;
                        const a_bound = Math.atan2(S - R, S);
                        if (oct <= a_bound) {{
                            r = S / Math.cos(oct);
                        }} else {{
                            const cx = S - R, cy = S - R;
                            const b = cx * Math.cos(oct) + cy * Math.sin(oct);
                            const c = cx * cx + cy * cy - R * R;
                            r = b + Math.sqrt(b * b - c);
                        }}
                    }}
                    else if (type === 'peanut') {{
                        const W = 48;
                        const H = 34;
                        const cx = W - H;
                        let quad = a % Math.PI;
                        if (quad > Math.PI / 2) quad = Math.PI - quad;
                        const a_bound = Math.atan2(H, cx);
                        if (quad >= a_bound) {{
                            r = H / Math.sin(quad);
                        }} else {{
                            const b = cx * Math.cos(quad);
                            const c = cx * cx - H * H;
                            r = b + Math.sqrt(b * b - c);
                        }}
                    }}
                    const x = centerX + r * Math.cos(angle);
                    const y = centerY + r * Math.sin(angle);
                    if (i === 0) d += `M ${{x.toFixed(2)}},${{y.toFixed(2)}} `;
                    else d += `L ${{x.toFixed(2)}},${{y.toFixed(2)}} `;
                }}
                return d + "Z";
            }}
            const pFlower = generateGeometricPath('flower');
            const pBlob = generateGeometricPath('blob');
            const pPeanut = generateGeometricPath('peanut');
            const animValues = `${{pFlower}}; ${{pFlower}}; ${{pBlob}}; ${{pBlob}}; ${{pFlower}}; ${{pFlower}}; ${{pPeanut}}; ${{pPeanut}}; ${{pFlower}}`;
            const keyTimes = "0; 0.15; 0.25; 0.40; 0.50; 0.65; 0.75; 0.90; 1";
            const holdSpline = "0 0 1 1";
            const morphSpline = "0.2 0.0 0.0 1.0";
            const keySplines = [
                holdSpline, morphSpline,
                holdSpline, morphSpline,
                holdSpline, morphSpline,
                holdSpline, morphSpline
            ].join('; ');
            document.querySelectorAll('.morph-anim').forEach(anim => {{
                anim.setAttribute('values', animValues);
                anim.setAttribute('keyTimes', keyTimes);
                anim.setAttribute('keySplines', keySplines);
            }});
            document.querySelectorAll('.morph-path').forEach(p => {{
                p.setAttribute('d', pFlower);
            }});
        }});
    </script>
</body>
</html>
"""

_kpm_instance = None

def _kpm_logs_enabled():
    inst = globals().get("_kpm_instance")
    if inst is None:
        return True
    try:
        return bool(inst.get_setting("logs_enabled", True))
    except Exception:
        return True

def log(*args, **kwargs):
    try:
        if _kpm_logs_enabled():
            _android_log(*args, **kwargs)
    except Exception:
        pass

def _get_lang():
    lang = Locale.getDefault().getLanguage().lower()
    if lang.startswith("ru"):
        return "ru"
    elif lang.startswith("uk") or lang.startswith("ua"):
        return "uk"
    else:
        return "en"

_KPM_LOCALE = {}
_KPM_LOCALE_LOADED = False


def _load_kpm_locale():
    global _KPM_LOCALE, _KPM_LOCALE_LOADED
    if _KPM_LOCALE_LOADED:
        return
    try:
        _locale_path = os.path.join(os.path.dirname(__file__), "assests", "locale.json")
        if os.path.isfile(_locale_path):
            with open(_locale_path, "r", encoding="utf-8") as _f:
                _KPM_LOCALE = json.load(_f)
        _KPM_LOCALE_LOADED = True
    except Exception:
        _KPM_LOCALE = {}
        _KPM_LOCALE_LOADED = True


def _tr(key):
    _load_kpm_locale()
    lang = _get_lang()
    lang_dict = _KPM_LOCALE.get(lang) or _KPM_LOCALE.get("en", {})
    return lang_dict.get(key, key)

def _status_label(status: str):
    try:
        s = (status or "plugin").lower()
    except Exception:
        s = "plugin"
    if s == "library":
        return _tr("status_library")
    if s == "customization":
        return _tr("status_customization")
    if s == "utilities":
        return _tr("status_utilities")
    if s == "informational":
        return _tr("status_informational")
    if s == "fun":
        return _tr("status_fun")
    if s == "messages":
        return _tr("status_messages")
    return _tr("status_plugin")

def _status_sort_key(status: str):
    try:
        s = (status or "plugin").lower()
    except Exception:
        s = "plugin"
    order = {
        "library": 0,
        "customization": 1,
        "utilities": 2,
        "informational": 3,
        "messages": 4,
        "fun": 5,
    }
    return order.get(s, 99)


def _normalize_requirements_list(value):
    if not value:
        return []
    if isinstance(value, (list, tuple, set)):
        items = list(value)
    else:
        items = str(value).split(",")
    result = []
    for item in items:
        text = str(item).strip()
        if text and text not in result:
            result.append(text)
    return result


def _normalize_min_version(value):
    if not value:
        return ""
    match = re.search(r"(\d+(?:\.\d+)+)", str(value))
    return match.group(1) if match else str(value).strip()


def _format_badge_compact(prefix: str, values, max_items: int = 2):
    parts = _normalize_requirements_list(values)
    if not parts:
        return ""
    text = ", ".join(parts[:max_items])
    if len(parts) > max_items:
        text += f" +{len(parts) - max_items}"
    return f"{prefix} {text}".strip()

def _parse_markdown(text: str, text_color: int = None):
    if not text:
        return None, text

    try:
        from android.text import SpannableString
        from android.text.style import StyleSpan, URLSpan, ForegroundColorSpan
        from android.graphics import Typeface
        def to_java_pos(py_pos, original_text):
            java_pos = 0
            for i, char in enumerate(original_text):
                if i >= py_pos:
                    break
                if ord(char) > 0xFFFF:
                    java_pos += 2
                else:
                    java_pos += 1
            return java_pos
        
        spans = []
        plain_text = text

        def apply_pattern(source_text, pattern, span_factory, text_getter):
            local_spans = []
            cursor = 0
            parts = []
            for match in pattern.finditer(source_text):
                parts.append(source_text[cursor:match.start()])
                replacement = text_getter(match)
                start = sum(len(part) for part in parts)
                end = start + len(replacement)
                span_obj = span_factory(match)
                if isinstance(span_obj, (list, tuple)):
                    for item in span_obj:
                        local_spans.append((start, end, item, match.start(), match.end()))
                else:
                    local_spans.append((start, end, span_obj, match.start(), match.end()))
                parts.append(replacement)
                cursor = match.end()
            parts.append(source_text[cursor:])
            return "".join(parts), local_spans

        plain_text, local_spans = apply_pattern(
            plain_text,
            re.compile(r'\*\*(.+?)\*\*'),
            lambda match: StyleSpan(Typeface.BOLD),
            lambda match: match.group(1)
        )
        spans.extend(local_spans)

        plain_text, local_spans = apply_pattern(
            plain_text,
            re.compile(r'(?<!\*)\*(?!\*)(.+?)(?<!\*)\*(?!\*)'),
            lambda match: StyleSpan(Typeface.ITALIC),
            lambda match: match.group(1)
        )
        spans.extend(local_spans)

        plain_text, local_spans = apply_pattern(
            plain_text,
            re.compile(r'\[([^\]]+)\]\(([^)]+)\)'),
            lambda match: URLSpan(match.group(2)),
            lambda match: match.group(1)
        )
        spans.extend(local_spans)

        offset = 0
        text = plain_text
        plain_text = text
        mention_pattern = re.compile(r'@([a-zA-Z0-9_]+)')
        for match in mention_pattern.finditer(text):
            start = match.start() - offset
            username = match.group(1)
            end = start + len(match.group(0))
            url = f"tg://resolve?domain={username}"
            spans.append((start, end, URLSpan(url), match.start(), match.end()))
            if text_color is not None:
                spans.append((start, end, ForegroundColorSpan(text_color), match.start(), match.end()))
        offset = 0
        text = plain_text
        plain_text = text
        url_pattern = re.compile(r'(https?://[^\s\)\]\n]+)')
        for match in url_pattern.finditer(text):
            start = match.start() - offset
            url = match.group(1)
            end = start + len(url)
            spans.append((start, end, URLSpan(url), match.start(), match.end()))
            if text_color is not None:
                spans.append((start, end, ForegroundColorSpan(text_color), match.start(), match.end()))
        java_spans = []
        java_len = to_java_pos(len(plain_text), plain_text) 
        for start, end, span, orig_start, orig_end in spans:
            java_start = to_java_pos(start, plain_text)
            java_end = to_java_pos(end, plain_text)
            java_spans.append((java_start, java_end, span))
        
        result = SpannableString(plain_text)
        for start, end, span in java_spans:
            try:
                if start >= 0 and end <= java_len and start < end:
                    result.setSpan(span, start, end, SpannableString.SPAN_EXCLUSIVE_EXCLUSIVE)
                else:
                    log(f"[KPM] Span rejected: {start}-{end} outside range 0-{java_len}")
            except Exception as e:
                log(f"[KPM] Span error: {e}")
        
        return result, plain_text
    except Exception as e:
        log(f"[KPM] Markdown parse error: {e}")
        return None, text

def open_link(url):
    log(f"[KPM] open_link requested: url={url}")

    def go():
        fragment = None
        context = None
        try:
            fragment = get_last_fragment()
            log(f"[KPM] open_link fragment={fragment}")
        except Exception as e:
            log(f"[KPM] open_link get_last_fragment error: {e}")

        try:
            if fragment:
                context = fragment.getParentActivity()
            log(f"[KPM] open_link parentActivity={context}")
        except Exception as e:
            log(f"[KPM] open_link getParentActivity error: {e}")

        if context is None:
            try:
                from org.telegram.messenger import ApplicationLoader
                context = ApplicationLoader.applicationContext
                log(f"[KPM] open_link applicationContext fallback={context}")
            except Exception as e:
                log(f"[KPM] open_link applicationContext error: {e}")

        if context is None:
            log("[KPM] open_link aborted: no context")
            return

        try:
            Browser = None
            try:
                from org.telegram.messenger.browser import Browser
            except Exception:
                try:
                    from hook_utils import find_class
                    Browser = find_class("org.telegram.messenger.browser.Browser")
                except Exception as e:
                    log(f"[KPM] open_link Browser resolve error: {e}")
            if Browser is not None:
                log(f"[KPM] open_link via Browser.openUrl: {url}")
                Browser.openUrl(context, url)
                return
            log("[KPM] open_link Browser unavailable, falling back to ACTION_VIEW")
        except Exception as e:
            log(f"[KPM] open_link Browser.openUrl error: {e}")

        try:
            intent = Intent(Intent.ACTION_VIEW, Uri.parse(url))
            log(f"[KPM] open_link ACTION_VIEW intent={intent}")
            context.startActivity(intent)
            log("[KPM] open_link ACTION_VIEW startActivity ok")
        except Exception as e:
            log(f"[KPM] open_link ACTION_VIEW error: {e}")

    run_on_ui_thread(go)


def _get_current_account(fragment):
    try:
        account = fragment.getCurrentAccount()
        log(f"[KPM] _get_current_account via getCurrentAccount={account}")
        return account
    except Exception:
        try:
            account = fragment.currentAccount
            log(f"[KPM] _get_current_account via currentAccount={account}")
            return account
        except Exception as e:
            log(f"[KPM] _get_current_account failed: {e}")
            return 0


def open_username(username):
    log(f"[KPM] open_username requested: username={username}")

    def go():
        try:
            fragment = get_last_fragment()
            if not fragment:
                log("[KPM] open_username aborted: no fragment")
                return
            account = _get_current_account(fragment)
            log(f"[KPM] open_username fragment={fragment} account={account}")
            ok = False
            try:
                ok = get_messages_controller().openByUserName(username, fragment, account)
                log(f"[KPM] open_username openByUserName result={ok}")
            except Exception as e:
                log(f"[KPM] openByUserName error: {e}")
            if not ok:
                try:
                    context = fragment.getParentActivity()
                    if context:
                        log(f"[KPM] open_username fallback tg://resolve context={context}")
                        intent = Intent(Intent.ACTION_VIEW, Uri.parse(f"tg://resolve?domain={username}"))
                        context.startActivity(intent)
                        log("[KPM] open_username tg://resolve startActivity ok")
                        return
                    log("[KPM] open_username fallback tg://resolve skipped: no context")
                except Exception as e2:
                    log(f"[KPM] tg://resolve fallback error: {e2}")
                log(f"[KPM] open_username falling back to https://t.me/{username}")
                open_link(f"https://t.me/{username}")
        except Exception as e:
            log(f"[KPM] open_username error: {e}")
            open_link(f"https://t.me/{username}")
    run_on_ui_thread(go)

class KPMSettingsHeaderHook:
    def __init__(self, plugin):
        self.plugin = plugin
    
    def after_hooked_method(self, param):
        try:
            activity = param.thisObject
            items = param.args[0]
            if not items or items.size() == 0:
                return
            
            plugin_obj = get_private_field(activity, "plugin")
            if not plugin_obj or str(plugin_obj.getId()) != "kangel_plugins_manager":
                return
            
            if get_private_field(activity, "createSubFragmentCallback") is not None:
                return
            
            header = self.plugin._create_settings_header(activity.getContext())
            if header:
                from com.exteragram.messenger.plugins.models import \
                    HeaderSetting
                from org.telegram.ui.Components import UItem
                item = UItem.asCustom(header)
                item.settingItem = HeaderSetting("kpm_header")
                try: 
                    item.setTransparent(True)
                except: 
                    pass
                items.add(0, item)
                items.add(1, UItem.asShadow())
        except Exception as e:
            log(f"[KPM] Error in settings header hook: {e}")
