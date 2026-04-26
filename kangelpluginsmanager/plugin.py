import os
import re
import weakref
import requests
import json
import time
import traceback
import shutil

from android import R as android_R
from android.content import ClipboardManager, ClipData, Context, Intent
from android.graphics.drawable import InsetDrawable
from android.net import Uri
from android.text import SpannableString, Spanned, TextWatcher, TextUtils
from android.text.style import StrikethroughSpan
from android.util import TypedValue
from android.view import Gravity, View, ViewGroup
from android.view.animation import OvershootInterpolator
from android.widget import (AbsListView, AdapterView, ArrayAdapter, BaseAdapter,
                             EditText, FrameLayout, ImageView, LinearLayout, ListView, TextView)
from android.widget import TextView as AndroidTextView
from android_utils import log as _android_log, run_on_ui_thread
from androidx.core.widget import NestedScrollView
from base_plugin import BasePlugin, MenuItemData, MenuItemType, MethodHook
from client_utils import (get_last_fragment, get_messages_controller,
                          run_on_queue, send_document, send_message)
from file_utils import get_plugins_dir
from com.exteragram.messenger.plugins import Plugin, PluginsController
from com.exteragram.messenger.plugins.ui import PluginSettingsActivity
from com.exteragram.messenger.plugins.ui.components import PluginCellDelegate
from com.exteragram.messenger.plugins.ui.components.templates import UniversalFragment
from hook_utils import find_class, get_private_field
from java import dynamic_proxy, jint
from java.lang import String
from java.util import ArrayList, Locale
from org.telegram.messenger import (AndroidUtilities, ApplicationLoader,
                                    ImageLocation, MediaDataController, NotificationCenter)
from org.telegram.messenger import R as R_tg
from org.telegram.messenger import Utilities
from org.telegram.tgnet import TLRPC
from org.telegram.ui.ActionBar import ActionBar, AlertDialog, BottomSheet, SimpleTextView, Theme
from org.telegram.ui.Components import BackupImageView, LayoutHelper, UItem, UniversalRecyclerView
from ui.alert import AlertDialogBuilder
from ui.bulletin import BulletinHelper
from ui.settings import Divider, Header, Input, Selector, Switch, Text

from .methods import (
    _get_loading_html,
    _kpm_logs_enabled,
    log,
    _get_lang,
    _tr,
    _status_label,
    _status_sort_key,
    _parse_markdown,
    open_link,
    _get_current_account,
    open_username,
    KPMSettingsHeaderHook,
    _normalize_requirements_list,
    _normalize_min_version,
    _format_badge_compact,
)
from .sbroka import (
    build_collection_payload,
    export_collection,
    import_collection,
    normalize_collection_plugins,
)

__id__ = "kangel_plugins_manager"
__name__ = "Kangel Plugins Manager"
__description__ = """
Первый магазин плагинов , предлагающий удобное управление плагинами
Требования: exteraGram/Ayugram 12.5.1 и выше

First plugin store with easy plugin management
Requirements:exteraGram/AyuGram 12.5.1 or higher
"""
__author__ = "@ArThirtyFour | @KangelPlugins"
__min_version__ = "12.5.1"
__icon__ = "Kangelcons_by_fStikBot/5"
__version__ = "1.4.1"

PLUGINS_DIR = get_plugins_dir()
KPM_PILL_ID = 34012501
KPM_PILL_TAG = "kpm_pill"


class KangelPluginsManagerPlugin(BasePlugin):
    pass

    def has_settings(self):
        return True

    def _ensure_plugins_dir(self):
        self.plugins_dir = PLUGINS_DIR
        try:
            os.makedirs(self.plugins_dir, exist_ok=True)
        except Exception as e:
            log(f"[KPM] plugins dir create failed: {e}")
        self.cache_file = os.path.join(self.plugins_dir, ".kpm_cache.json")
        return self.plugins_dir

    def _plugins_path(self, *parts):
        return os.path.join(self._ensure_plugins_dir(), *parts)

    def _read_plugin_file_info(self, file_path):
        try:
            if not file_path or not os.path.exists(file_path):
                return None, None
            with open(file_path, "rb") as f:
                content = f.read()
            metadata = self.parse_plugin_metadata(content)
            plugin_id = None
            try:
                text = content.decode("utf-8", errors="ignore")
                id_match = re.search(r'__id__\s*=\s*["\']([^"\']+)["\']', text)
                if id_match:
                    plugin_id = id_match.group(1)
            except Exception:
                pass
            if not plugin_id:
                plugin_id = os.path.basename(str(file_path)).replace(".plugin", "").replace(".py", "").strip()
            if plugin_id.startswith(".temp_"):
                plugin_id = plugin_id.replace(".temp_", "")
            return plugin_id, metadata
        except Exception as e:
            log(f"[KPM] Failed to read plugin file info from {file_path}: {e}")
            return None, None

    def _block_install_dialog_if_unsupported(self, file_path):
        try:
            try:
                if not bool(self.get_setting("enforce_version_requirements", True)):
                    return False
            except Exception:
                pass
            plugin_id, metadata = self._read_plugin_file_info(file_path)
            if not plugin_id or not isinstance(metadata, dict):
                return False
            min_version = metadata.get("min_version") or ""
            if not min_version:
                return False
            client_version = self._mkstats_get_client_version() or "unknown"
            if self._is_client_version_at_least(min_version):
                return False
            log(f"[KPM] Blocking install dialog for {plugin_id}: requires {min_version}, client is {client_version}")
            run_on_ui_thread(lambda pid=plugin_id, mv=min_version, cv=client_version: self._show_requirements_dialog(pid, mv, cv))
            return True
        except Exception as e:
            log(f"[KPM] Failed to guard install dialog for {file_path}: {e}")
            return False

    def _is_client_version_at_least(self, min_version: str) -> bool:
        try:
            client_version = self._mkstats_get_client_version()
            if not client_version or client_version == "unknown":
                return False
            return self._compare_versions(client_version, min_version) >= 0
        except Exception:
            return False

    def _get_plugin_version_state(self, plugin_id, plugin_info=None):
        try:
            full_info = self.get_plugin_full_info(plugin_id)
            if isinstance(full_info, dict):
                plugin_info = full_info
            elif plugin_info is None:
                plugin_info = self.plugins_list.get(plugin_id)
            min_version = ""
            if isinstance(plugin_info, dict):
                min_version = plugin_info.get("min_version", "") or _normalize_min_version(plugin_info.get("app_version", ""))
            client_version = self._mkstats_get_client_version() or "unknown"
            compatible = True
            if min_version:
                compatible = self._is_client_version_at_least(min_version)
            return min_version, client_version, compatible
        except Exception:
            return "", "unknown", True

    def _ensure_plugin_version_supported(self, plugin_id, plugin_info=None, show_dialog=True):
        try:
            if not bool(self.get_setting("enforce_version_requirements", True)):
                return True
        except Exception:
            pass
        min_version, client_version, compatible = self._get_plugin_version_state(plugin_id, plugin_info)
        if compatible or not min_version:
            return True
        if show_dialog:
            run_on_ui_thread(lambda: self._show_requirements_dialog(plugin_id, min_version, client_version))
        return False

    def _pill_supported(self) -> bool:
        return self._is_client_version_at_least("12.5")

    def _register_kpm_pill(self):
        try:
            enabled = bool(self.get_setting("pill_enabled", True))
        except Exception:
            enabled = False
        if not enabled:
            log("[KPM] Pill disabled in settings")
            self._pill_registered = False
            return
        if not self._pill_supported():
            log("[KPM] Pill unsupported on this client version")
            self._pill_registered = False
            return
        if not self.PillRegistry or not self.PillInfo or not self.PillCreator or not self.PillStackConfig or not self.WeatherPill:
            log("[KPM] Pill classes unavailable")
            self._pill_registered = False
            return
        if self._pill_registered:
            self._ensure_kpm_pill_visible()
            self._update_all_pills()
            return

        plugin = self

        class KPMPillCreator(dynamic_proxy(plugin.PillCreator)):
            def __init__(self):
                super().__init__()

            def create(self, context, resourcesProvider):
                try:
                    pill = plugin.WeatherPill(context, resourcesProvider)
                    pill.setTag(KPM_PILL_TAG)
                    plugin._active_pills.add(pill)
                    plugin._apply_kpm_pill_ui(pill)
                    log("[KPM] KPMPillCreator.create: pill instance created")
                    return pill
                except Exception as e:
                    log(f"[KPM] KPMPillCreator.create failed: {e}")
                    log(traceback.format_exc())
                    return None

        try:
            info = self.PillInfo(
                jint(KPM_PILL_ID),
                _tr("pill_title"),
                jint(R_tg.drawable.msg_addbot),
                jint(-11565578),
                jint(-13276952),
                KPMPillCreator()
            )
            self.PillRegistry.register(info)
            self._install_kpm_pill_hooks()
            self._ensure_kpm_pill_visible()
            self._pill_registered = True
            log("[KPM] Pill registered in registry")
            self._update_all_pills()
        except Exception as e:
            self._pill_registered = False
            log(f"[KPM] _register_kpm_pill failed: {e}")
            log(traceback.format_exc())

    def _update_all_pills(self):
        try:
            if not self._pill_supported():
                self._pill_registered = False
                return
            if bool(self.get_setting("pill_enabled", True)):
                self._register_kpm_pill()
                for pill in list(self._active_pills):
                    self._apply_kpm_pill_ui(pill)
            else:
                self._pill_registered = False
        except Exception as e:
            log(f"[KPM] Error updating pills: {e}")
            log(traceback.format_exc())

    def _install_kpm_pill_hooks(self):
        if self._pill_hooks_installed or not self.WeatherPill:
            return
        plugin = self

        class KPMGetIdHook(MethodHook):
            def before_hooked_method(self, param):
                try:
                    tag = param.thisObject.getTag()
                    if tag == KPM_PILL_TAG:
                        plugin._active_pills.add(param.thisObject)
                        param.setResult(jint(KPM_PILL_ID))
                except Exception as e:
                    log(f"[KPM] KPMGetIdHook failed: {e}")

        class KPMInteractionHook(MethodHook):
            def before_hooked_method(self, param):
                try:
                    tag = param.thisObject.getTag()
                    if tag != KPM_PILL_TAG:
                        return
                    plugin._active_pills.add(param.thisObject)
                    method_name = param.method.getName()
                    if method_name == "onPillClicked":
                        plugin._handle_kpm_pill_click()
                        param.setResult(None)
                    elif method_name == "onPillLongClicked":
                        plugin.open_settings_page()
                        param.setResult(True)
                    elif method_name in ["onUpdateData", "setData"]:
                        plugin._apply_kpm_pill_ui(param.thisObject)
                        param.setResult(None)
                except Exception as e:
                    log(f"[KPM] KPMInteractionHook failed: {e}")
                    log(traceback.format_exc())
                    
        class GetPillHook(MethodHook):
            def after_hooked_method(self, param):
                try:
                    num = param.args[0]
                    if num is not None:
                        pill_id = int(num.intValue())
                        pill = param.getResult()
                        if pill_id == KPM_PILL_ID and pill:
                            pill.setTag(KPM_PILL_TAG)
                            plugin._active_pills.add(pill)
                            plugin._apply_kpm_pill_ui(pill)
                except Exception as e:
                    pass

        try:
            self.hook_all_methods(self.WeatherPill.getClass(), "getPillId", KPMGetIdHook())
            self.hook_all_methods(self.WeatherPill.getClass(), "onPillClicked", KPMInteractionHook())
            self.hook_all_methods(self.WeatherPill.getClass(), "onPillLongClicked", KPMInteractionHook())
            self.hook_all_methods(self.WeatherPill.getClass(), "onUpdateData", KPMInteractionHook())
            self.hook_all_methods(self.WeatherPill.getClass(), "setData", KPMInteractionHook())
            FragmentSearchField = find_class("org.telegram.ui.Components.FragmentSearchField")
            if FragmentSearchField:
                self.hook_all_methods(FragmentSearchField.getClass(), "getPill", GetPillHook())
            self._pill_hooks_installed = True
            log("[KPM] Pill hooks installed")
        except Exception as e:
            log(f"[KPM] _install_kpm_pill_hooks failed: {e}")
            log(traceback.format_exc())

    def _ensure_kpm_pill_visible(self):
        try:
            active = self.PillStackConfig.activePills
            for i in range(active.size()):
                if int(active.get(i)) == KPM_PILL_ID:
                    log("[KPM] Pill already active in PillStackConfig")
                    return
            active.add(jint(KPM_PILL_ID))
            self.PillStackConfig.savePillsLayout()
            run_on_ui_thread(self.PillStackConfig.notifySettingsChanged)
            log("[KPM] Pill added to PillStackConfig.activePills")
        except Exception as e:
            log(f"[KPM] _ensure_kpm_pill_visible failed: {e}")
            log(traceback.format_exc())

    def _apply_kpm_pill_ui(self, pill):
        try:
            count = len(self.plugins_list or {})
            text_view = get_private_field(pill, "textView")
            if text_view:
                text_view.setText(_tr("pill_store_count").format(count))
            icon_view = get_private_field(pill, "iconView")
            if icon_view:
                try:
                    icon_view.setImageResource(R_tg.drawable.msg_addbot)
                except Exception:
                    pass
            log(f"[KPM] _apply_kpm_pill_ui: count={count}")
        except Exception as e:
            log(f"[KPM] _apply_kpm_pill_ui failed: {e}")

    def _handle_kpm_pill_click(self):
        try:
            action = int(self.get_setting("pill_click_action", 0) or 0)
        except Exception:
            action = 0
        log(f"[KPM] Pill clicked, action={action}")
        if action == 1:
            self.open_update_dialog()
        elif action == 2:
            run_on_queue(lambda: self.refresh_store(force=True, has_bulletin=True, md3_anim=False))
        elif action == 3:
            self.open_settings_page()
        else:
            self.open_install_dialog()

    def _open_faq(self, *_):
        try:
            lang = str(LocaleController.getInstance().getCurrentLocale().getLanguage())
        except Exception:
            lang = "en"
        if lang == "ru":
            open_link("https://t.me/KangelPluginsManager/166/172")
        else:
            open_link("https://t.me/KangelPluginsManager/166/6441")

    def create_settings(self):
        log("[KPM] create_settings: start")
        try:
            items = [
                Header(text=_tr("header")),
                Text(
                    text=_tr("plugin_management"),
                    icon="msg_addbot",
                    create_sub_fragment=self._create_plugin_management_settings
                ),
                Text(
                    text=_tr("auto_updates"),
                    icon="files_storage",
                    create_sub_fragment=self._create_auto_updates_settings
                ),
                Text(
                    text=_tr("ui_settings"),
                    icon="msg_theme",
                    create_sub_fragment=self._create_ui_settings
                ),
                Text(
                    text=_tr("other_settings"),
                    icon="msg_info",
                    create_sub_fragment=self._create_other_settings
                ),
                Text(
                    text=_tr("about_plugin"),
                    icon="mentionbutton",
                    create_sub_fragment=self._create_about_settings
                )
            ]
            log(f"[KPM] create_settings: done items={len(items)}")
            return items
        except Exception as e:
            log(f"[KPM] create_settings failed: {e}")
            log(traceback.format_exc())
            return [
                Header(text=_tr("header")),
                Text(text=f"Settings crash: {e}", red=True)
            ]
    
    def _create_plugin_management_settings(self):
        items = [
            Header(text=_tr("actions_header")),
            Text(
                text=_tr("refresh_list"),
                icon="msg_download",
                on_click=lambda _: run_on_queue(lambda: self.refresh_store())
            ),
            Text(
                text=_tr("install_plugin"),
                icon="msg_addbot",
                on_click=lambda _: self.open_install_dialog()
            ),
            Text(
                text=_tr("update_plugins"),
                icon="menu_browser_refresh",
                on_click=lambda _: self.open_update_dialog()
            ),
            Text(
                text=_tr("clear_cache"),
                icon="msg_clear",
                on_click=lambda _: run_on_queue(lambda: self.clear_cache())
            ),
            Divider(),
            Header(text=_tr("plugin_collections")),
            Text(
                text=_tr("export_collection"),
                icon="msg_share",
                on_click=lambda _: open_link("https://github.com/KangelPlugins/SborkaDocs/blob/main/README.md")
            ),
            Text(
                text=_tr("import_collection"),
                icon="msg_download",
                on_click=lambda _: self._show_import_collection_dialog()
            )
        ]
        return items

    def _get_store_picker_plugin_ids(self):
        if not self.plugins_list:
            self.load_cache()
        if not self.plugins_list:
            self.refresh_store(force=True, has_bulletin=False, md3_anim=False)
        return sorted(list(self.plugins_list.keys()), key=lambda pid: self.get_plugin_display_name(pid).lower())

    def _make_collection_preview_text(self, metadata, plugin_ids):
        plugin_ids = normalize_collection_plugins(plugin_ids)
        lines = []
        name = str((metadata or {}).get("name") or "").strip()
        author = str((metadata or {}).get("author") or "").strip()
        description = str((metadata or {}).get("description") or "").strip()
        
        if name:
            lines.append(name)
        if author:
            lines.append(f"{_tr('collection_author')}: {author}")
        if description:
            lines.append(description)
            
        count_label = _tr("collection_plugins_count").format(len(plugin_ids))
        lines.append(count_label)
        if plugin_ids:
            preview = []
            for pid in plugin_ids[:6]:
                info = self.plugins_list.get(pid) or {}
                preview.append(f"• {info.get('name', pid)}")
            if len(plugin_ids) > 6:
                preview.append(_tr("collection_plugins_more").format(len(plugin_ids) - 6))
            lines.append("\n".join(preview))
        else:
            lines.append(_tr("collection_plugins_empty"))
        return "\n\n".join([line for line in lines if line])

    def _show_collection_picker(self, title, selected_plugin_ids, on_done):
        log(f"[KPM] _show_collection_picker called with title: {title}, selected_plugin_ids: {selected_plugin_ids}")
        fragment = get_last_fragment()
        if not fragment:
            log("[KPM] _show_collection_picker: fragment is None, returning")
            return

        all_ids = self._get_store_picker_plugin_ids()
        log(f"[KPM] _show_collection_picker: all_ids: {all_ids}")
        if not all_ids:
            BulletinHelper.show_error(_tr("store_load_failed"))
            return

        initial_selected = set(normalize_collection_plugins(selected_plugin_ids))
        
        delegate = self.CollectionPickerFragment(self, title, all_ids, initial_selected, on_done)
        picker_fragment = UniversalFragment(delegate)
        fragment.presentFragment(picker_fragment)

    def _show_collection_designer(self, mode, metadata=None, selected_plugin_ids=None):
        fragment = get_last_fragment()
        if not fragment:
            return
        metadata = dict(metadata or {})
        selected_plugin_ids = normalize_collection_plugins(selected_plugin_ids or [])
        context = fragment.getParentActivity()
        if not context:
            return

        from org.telegram.ui.Components import EditTextBoldCursor

        builder = AlertDialogBuilder(context)
        
        container = LinearLayout(context)
        container.setOrientation(LinearLayout.VERTICAL)
        container.setPadding(AndroidUtilities.dp(18), AndroidUtilities.dp(10), AndroidUtilities.dp(18), AndroidUtilities.dp(6))
        if mode == "import":
            builder.set_title(_tr("import_collection"))
            
            preview_card = LinearLayout(context)
            preview_card.setOrientation(LinearLayout.VERTICAL)
            preview_card.setPadding(AndroidUtilities.dp(16), AndroidUtilities.dp(16), AndroidUtilities.dp(16), AndroidUtilities.dp(16))
            try:
                preview_card.setBackground(Theme.createRoundRectDrawable(AndroidUtilities.dp(24), Theme.getColor(Theme.key_dialogSearchBackground)))
            except Exception:
                pass
            header_row = LinearLayout(context)
            header_row.setOrientation(LinearLayout.HORIZONTAL)
            header_row.setGravity(Gravity.CENTER_VERTICAL)
            icon_view = BackupImageView(context)
            icon_view.setRoundRadius(0)
            icon_view.getImageReceiver().setCrossfadeWithOldImage(True)
            icon_str = metadata.get("icon", "")
            if "/" in icon_str:
                parts = icon_str.split("/", 1)
                if len(parts) == 2:
                    pack_name, index_str = parts
                    try:
                        sticker_index = int(index_str)
                        self._load_sticker_async(icon_view, pack_name, sticker_index, f"col_icon_{pack_name}_{sticker_index}")
                    except ValueError:
                        pass
            header_row.addView(icon_view, LayoutHelper.createLinear(40, 40, 0, 0, 12, 0))

            coll_name = metadata.get("name", "Unnamed Collection")
            title_text = AndroidTextView(context)
            title_text.setText(coll_name)
            title_text.setTypeface(AndroidUtilities.bold())
            title_text.setTextSize(18)
            title_text.setTextColor(Theme.getColor(Theme.key_dialogTextBlack))
            header_row.addView(title_text, LayoutHelper.createLinear(-1, -2))

            preview_card.addView(header_row, LayoutHelper.createLinear(-1, -2))

            coll_desc = metadata.get("description", "")
            if coll_desc:
                desc_text = AndroidTextView(context)
                desc_text.setText(coll_desc)
                desc_text.setTextSize(14)
                desc_text.setTextColor(Theme.getColor(Theme.key_dialogTextGray2))
                desc_text.setPadding(0, AndroidUtilities.dp(8), 0, 0)
                preview_card.addView(desc_text, LayoutHelper.createLinear(-1, -2))

            plugins_scroll = NestedScrollView(context)
            plugins_scroll.setPadding(0, AndroidUtilities.dp(8), 0, 0)
            
            plugins_layout = LinearLayout(context)
            plugins_layout.setOrientation(LinearLayout.VERTICAL)

            store_data = {}
            try:
                store_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "Plugins-Store", "store.json")
                if os.path.exists(store_path):
                    with open(store_path, "r", encoding="utf-8") as f:
                        store_data = json.load(f)
            except Exception:
                pass

            for plugin_id in selected_plugin_ids:
                plugin_name = store_data.get(plugin_id, {}).get("name", plugin_id) if isinstance(store_data.get(plugin_id), dict) else plugin_id
                
                plugin_row = LinearLayout(context)
                plugin_row.setOrientation(LinearLayout.HORIZONTAL)
                plugin_row.setGravity(Gravity.CENTER_VERTICAL)
                plugin_row.setPadding(0, AndroidUtilities.dp(4), 0, AndroidUtilities.dp(4))
                
                dot = AndroidTextView(context)
                dot.setText("•")
                dot.setTextSize(14)
                dot.setTextColor(Theme.getColor(Theme.key_windowBackgroundWhiteGreenText))
                dot.setPadding(0, 0, AndroidUtilities.dp(8), 0)
                plugin_row.addView(dot)
                
                name_text = AndroidTextView(context)
                name_text.setText(plugin_name)
                name_text.setTextSize(14)
                name_text.setTextColor(Theme.getColor(Theme.key_dialogTextBlack))
                plugin_row.addView(name_text, LayoutHelper.createLinear(-1, -2))
                
                plugins_layout.addView(plugin_row)
            
            plugins_scroll.addView(plugins_layout)
            container.addView(plugins_scroll)

            coll_author = metadata.get("author", "")
            if coll_author:
                author_text = AndroidTextView(context)
                author_text.setText(f"by {coll_author}")
                author_text.setTextSize(13)
                author_text.setTextColor(Theme.getColor(Theme.key_dialogTextGray))
                author_text.setPadding(0, AndroidUtilities.dp(4), 0, 0)
                preview_card.addView(author_text, LayoutHelper.createLinear(-1, -2))

            container.addView(preview_card)
            builder.set_view(container)

            def on_install(d, w):
                d.dismiss()
                self._import_collection_plugins(metadata, selected_plugin_ids)
            
            builder.set_positive_button(_tr("install_button"), on_install)
            builder.set_negative_button(_tr("cancel"), lambda d, w: d.dismiss())
            builder.show()
            return

        builder.set_title(_tr("export_collection"))

        def make_field(hint_key, value=""):
            field = EditTextBoldCursor(context)
            field.setHint(_tr(hint_key))
            field.setText(str(value or ""))
            try:
                field.setTextColor(Theme.getColor(Theme.key_dialogTextBlack))
                field.setHintTextColor(Theme.getColor(Theme.key_dialogTextGray))
                field.setTextSize(TypedValue.COMPLEX_UNIT_DIP, 16)
                field.setPadding(AndroidUtilities.dp(14), AndroidUtilities.dp(12), AndroidUtilities.dp(14), AndroidUtilities.dp(12))
                field.setBackground(Theme.createRoundRectDrawable(AndroidUtilities.dp(18), Theme.getColor(Theme.key_dialogSearchBackground)))
            except Exception:
                pass
            lp = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT)
            lp.bottomMargin = AndroidUtilities.dp(10)
            container.addView(field, lp)
            return field

        name_edit = make_field("collection_name", metadata.get("name", ""))
        author_edit = make_field("collection_author", metadata.get("author", ""))
        desc_edit = make_field("collection_description", metadata.get("description", ""))
        icon_edit = make_field("collection_icon", metadata.get("icon", ""))

        preview_card = LinearLayout(context)
        preview_card.setOrientation(LinearLayout.VERTICAL)
        preview_card.setPadding(AndroidUtilities.dp(16), AndroidUtilities.dp(16), AndroidUtilities.dp(16), AndroidUtilities.dp(16))
        try:
            preview_card.setBackground(Theme.createRoundRectDrawable(AndroidUtilities.dp(24), Theme.getColor(Theme.key_dialogSearchBackground)))
        except Exception:
            pass

        header_row = LinearLayout(context)
        header_row.setOrientation(LinearLayout.HORIZONTAL)
        header_row.setGravity(Gravity.CENTER_VERTICAL)

        icon_view = BackupImageView(context)
        icon_view.setRoundRadius(0)
        icon_view.getImageReceiver().setCrossfadeWithOldImage(True)
        icon_view.setVisibility(View.GONE)
        header_row.addView(icon_view, LayoutHelper.createLinear(40, 40, 0, 0, 12, 0))

        preview_title = AndroidTextView(context)
        preview_title.setText(_tr("collection_preview"))
        preview_title.setTypeface(AndroidUtilities.bold())
        preview_title.setTextSize(16)
        preview_title.setTextColor(Theme.getColor(Theme.key_dialogTextBlack))
        header_row.addView(preview_title, LayoutHelper.createLinear(-2, -2))

        preview_card.addView(header_row, LayoutHelper.createLinear(-1, -2))

        preview_text = AndroidTextView(context)
        preview_text.setTextSize(14)
        preview_text.setTextColor(Theme.getColor(Theme.key_dialogTextGray2))
        preview_text.setPadding(0, AndroidUtilities.dp(8), 0, 0)
        preview_card.addView(preview_text, LayoutHelper.createLinear(-1, -2))
        container.addView(preview_card)

        def current_metadata():
            return {
                "name": name_edit.getText().toString(),
                "author": author_edit.getText().toString(),
                "description": desc_edit.getText().toString(),
                "icon": icon_edit.getText().toString(),
            }

        def update_preview():
            md = current_metadata()
            preview_text.setText(self._make_collection_preview_text(md, selected_plugin_ids))
            icon_str = md.get("icon", "")
            if "/" in icon_str:
                parts = icon_str.split("/", 1)
                if len(parts) == 2:
                    pack_name, index_str = parts
                    try:
                        sticker_index = int(index_str)
                        icon_view.setVisibility(View.VISIBLE)
                        self._load_sticker_async(icon_view, pack_name, sticker_index, f"col_prev_{pack_name}_{sticker_index}")
                    except ValueError:
                        icon_view.setVisibility(View.GONE)
                else:
                    icon_view.setVisibility(View.GONE)
            else:
                icon_view.setVisibility(View.GONE)

        class PreviewWatcher(dynamic_proxy(TextWatcher)):
            def beforeTextChanged(self, s, start, count, after):
                pass
            def onTextChanged(self, s, start, before, count):
                pass
            def afterTextChanged(self, editable):
                update_preview()

        watcher = PreviewWatcher()
        name_edit.addTextChangedListener(watcher)
        author_edit.addTextChangedListener(watcher)
        desc_edit.addTextChangedListener(watcher)
        icon_edit.addTextChangedListener(watcher)
        update_preview()

        builder.set_view(container)
        builder.set_neutral_button(_tr("collection_pick_plugins"), lambda d, w: (d.dismiss(), self._show_collection_picker(_tr("collection_pick_plugins"), selected_plugin_ids, lambda ids: self._show_collection_designer(mode, current_metadata(), ids))))

        def on_submit(d, w):
            payload_metadata = current_metadata()
            self._import_collection_plugins(payload_metadata, selected_plugin_ids)
            d.dismiss()

        builder.set_positive_button(_tr("export_collection"), on_submit)
        builder.set_negative_button(_tr("cancel"), lambda d, w: d.dismiss())
        builder.show()

    def _show_import_collection_designer(self, metadata, plugin_ids):
        self._show_collection_designer("import", metadata, plugin_ids)

    def _import_collection_plugins(self, metadata, plugin_ids):
        plugin_ids = normalize_collection_plugins(plugin_ids)
        if not plugin_ids:
            BulletinHelper.show_error(_tr("collection_plugins_empty"))
            return

        run_on_ui_thread(lambda: BulletinHelper.show_info(f"Installing {len(plugin_ids)} plugins..."))

        def do_install_all():
            success_count = 0
            failed_count = 0
            for plugin_id in plugin_ids:
                try:
                    self.install_plugin_by_id(plugin_id, enable_after=True)
                    success_count += 1
                except Exception as e:
                    log(f"[KPM] Import install failed for {plugin_id}: {e}")
                    failed_count += 1
            
            if failed_count == 0:
                run_on_ui_thread(lambda: BulletinHelper.show_success(f"Successfully installed {success_count} plugins."))
            else:
                run_on_ui_thread(lambda: BulletinHelper.show_error(f"Installed {success_count} plugins, {failed_count} failed."))

        run_on_queue(do_install_all)
    
    
    def _create_auto_updates_settings(self):
        return [
            Header(text=_tr("updates_header")),
            Switch(
                key="auto_update_on_start",
                text=_tr("auto_update"),
                default=False,
                icon="files_storage",
                subtext=_tr("auto_update_sub")
            ),
            Switch(
                key="auto_update_installed",
                text=_tr("auto_update_installed"),
                default=False,
                icon="avd_flip",
                subtext=_tr("auto_update_installed_sub")
            )
        ]
    
    def _create_ui_settings(self):
        log("[KPM] _create_ui_settings: start")
        try:
            items = []

            def add(item_name, factory):
                log(f"[KPM] _create_ui_settings: building {item_name}")
                item = factory()
                items.append(item)
                log(f"[KPM] _create_ui_settings: added {item_name}")

            add("header_ui", lambda: Header(text=_tr("ui_settings")))
            add("show_drawer_menu", lambda: Switch(
                key="show_drawer_menu",
                text=_tr("show_drawer_menu"),
                default=True,
                icon="msg_addbot",
                subtext=_tr("show_drawer_menu_sub"),
                on_change=lambda v: self._update_drawer_menu()
            ))
            add("show_plugin_bubbles", lambda: Switch(
                key="show_plugin_bubbles",
                text=_tr("show_plugin_bubbles"),
                default=True,
                icon="files_internal_solar",
                subtext=_tr("show_plugin_bubbles_sub")
            ))
            add("show_add_button", lambda: Switch(
                key="show_add_button",
                text=_tr("show_add_button"),
                default=True,
                icon="msg_add",
                subtext=_tr("show_add_button_sub")
            ))
            add("show_update_button", lambda: Switch(
                key="show_update_button",
                text=_tr("show_update_button"),
                default=True,
                icon="menu_browser_refresh",
                subtext=_tr("show_update_button_sub")
            ))
            add("divider_inline", lambda: Divider())
            add("header_inline", lambda: Header(text=_tr("inline_search_header")))
            add("inline_search_enabled", lambda: Switch(
                key="inline_search_enabled",
                text=_tr("inline_search_enabled"),
                default=True,
                icon="msg_search",
                subtext=_tr("inline_search_enabled_sub")
            ))
            add("inline_search_trigger", lambda: Input(
                key="inline_search_trigger",
                text=_tr("inline_search_trigger"),
                default="kpm",
                icon="msg_bot",
                subtext=_tr("inline_search_trigger_sub")
            ))

            pill_supported = self._pill_supported()
            log(f"[KPM] _create_ui_settings: pill_supported={pill_supported}")
            if pill_supported:
                add("divider_pill", lambda: Divider())
                add("header_pill", lambda: Header(text=_tr("pill_header")))
                add("pill_enabled", lambda: Switch(
                    key="pill_enabled",
                    text=_tr("pill_enabled"),
                    default=True,
                    icon="msg_search",
                    subtext=_tr("pill_enabled_sub"),
                    on_change=lambda _: run_on_ui_thread(self._update_all_pills)
                ))
                add("pill_click_action", lambda: Selector(
                    key="pill_click_action",
                    text=_tr("pill_click_action"),
                    default=0,
                    items=[
                        _tr("pill_action_install"),
                        _tr("pill_action_update"),
                        _tr("pill_action_refresh"),
                        _tr("pill_action_settings"),
                    ],
                    icon="menu_more",
                    on_change=lambda _: run_on_ui_thread(self._update_all_pills)
                ))

            log(f"[KPM] _create_ui_settings: done, items={len(items)}")
            return items
        except Exception as e:
            log(f"[KPM] _create_ui_settings failed: {e}")
            log(traceback.format_exc())
            return [
                Header(text=_tr("ui_settings")),
                Text(text=f"UI settings crash: {e}", red=True)
            ]

    def _create_other_settings(self):
        return [
            Header(text=_tr("other_settings")),
            Switch(
                key="logs_enabled",
                text=_tr("logs"),
                default=True,
                icon="msg_info",
                subtext=_tr("logs_sub")
            ),
            Switch(
                key="enforce_version_requirements",
                text=_tr("version_guard"),
                default=True,
                icon="msg_warning",
                subtext=_tr("version_guard_sub")
            ),
            Divider(),
            Text(
                text=_tr("faq"),
                icon="msg_info",
                on_click=lambda _: self._open_faq()
            ),
        ]
    
    def _update_drawer_menu(self):
        try:
            self.add_drawer_menu_items()
        except Exception as e:
            log(f"[KPM] Error updating drawer menu: {e}")
    
    def _create_about_settings(self):
        return [
            Header(text=_tr("author_header")),
            Text(
                text=_tr("open_author_channel"),
                icon="input_smile_solar",
                on_click=lambda _: open_username("KangelPlugins")
            ),
            Text(
                text=_tr("open_forum"),
                icon="msg_groups_solar",
                on_click=lambda _: open_username("KangelPluginsManager")
            ),
            Text(
                text=_tr("send_to_bot"),
                icon="msg_forward",
                on_click=lambda _: open_username("KPMAppealBot")
            ),
            Text(
                text=_tr("open_github"),
                icon="msg_link",
                on_click=lambda _: open_link("https://github.com/KangelPlugins/Plugins-Store")
            ),
            Text(
                text=_tr("source_code"),
                icon="msg_link",
                on_click=lambda _: open_link("https://github.com/KangelPlugins/PluginManager")
            ),
            Divider(),
            Text(
                text=self._get_plugin_info_text(),
                icon="info",
                on_click=lambda _: self._show_about_dialog()
            )
        ]
    
    def _setup_settings_header_hook(self):
        try:
            PSA = find_class("com.exteragram.messenger.plugins.ui.PluginSettingsActivity")
            if not PSA:
                return
            method = PSA.getClass().getDeclaredMethod("fillItems", find_class("java.util.ArrayList"), find_class("org.telegram.ui.Components.UniversalAdapter"))
            method.setAccessible(True)
            self.hook_settings_header_ref = self.hook_method(method, KPMSettingsHeaderHook(self))
        except Exception as e:
            log(f"[KPM] Error setting up settings header hook: {e}")
    
    def _create_settings_header(self, context):
        try:
            from android.util import TypedValue
            from android.view import Gravity
            from android.widget import FrameLayout, LinearLayout, TextView
            from org.telegram.messenger import (AndroidUtilities,
                                                ImageLocation,
                                                MediaDataController)
            from org.telegram.ui.ActionBar import Theme
            from org.telegram.ui.Components import (BackupImageView,
                                                    LayoutHelper)
            
            container = FrameLayout(context)
            main_layout = LinearLayout(context)
            main_layout.setOrientation(LinearLayout.HORIZONTAL)
            main_layout.setGravity(Gravity.CENTER_VERTICAL)
            main_layout.setPadding(AndroidUtilities.dp(20), AndroidUtilities.dp(20), AndroidUtilities.dp(20), AndroidUtilities.dp(20))
            
            imageView = BackupImageView(context)
            imageView.setRoundRadius(0)
            def load_header_sticker():
                try:
                    icon_parts = __icon__.split("/")
                    if len(icon_parts) == 2:
                        sticker_set_name = icon_parts[0]
                        sticker_index = int(icon_parts[1])
                        self._load_sticker_async(imageView, sticker_set_name, sticker_index, f"header_sticker_{sticker_set_name}")
                except:
                    pass
            
            load_header_sticker()
            
            main_layout.addView(imageView, LayoutHelper.createLinear(72, 72, 0, 0, 16, 0))
            
            text_container = LinearLayout(context)
            text_container.setOrientation(LinearLayout.VERTICAL)
            text_container.setGravity(Gravity.CENTER_VERTICAL)
            
            title = TextView(context)
            title.setTextColor(Theme.getColor(Theme.key_windowBackgroundWhiteBlackText))
            title.setTypeface(AndroidUtilities.getTypeface(AndroidUtilities.TYPEFACE_ROBOTO_MEDIUM))
            title.setTextSize(TypedValue.COMPLEX_UNIT_DIP, 18)
            title.setText(f"{__name__} {__version__}")
            title.setSingleLine(True)
            title.setGravity(Gravity.START)
            text_container.addView(title, LayoutHelper.createLinear(-1, -2, 0, 0, 4, 0))
            subtitle_text = _tr("settings_subtitle")         
            subtitle = TextView(context)
            subtitle.setTextColor(Theme.getColor(Theme.key_windowBackgroundWhiteGrayText))
            subtitle.setTextSize(TypedValue.COMPLEX_UNIT_DIP, 14)
            subtitle.setText(subtitle_text)
            subtitle.setGravity(Gravity.START)
            text_container.addView(subtitle, LayoutHelper.createLinear(-1, -2))
            
            main_layout.addView(text_container, LayoutHelper.createLinear(0, -2, 1.0))
            container.addView(main_layout, LayoutHelper.createFrame(-1, -2, Gravity.TOP | Gravity.START, 0, 0, 0, 0))
            
            return container
        except Exception as e:
            log(f"[KPM] Error creating settings header: {e}")
            return None
    
    def _get_plugin_info_text(self):
        plugin_count = len(self.plugins_list) if self.plugins_list else 0
        return _tr("plugin_info_text").format(__version__, plugin_count)

    def _show_md3_loading(self, duration_ms=3000):
        try:
            fragment = get_last_fragment()
            if not fragment:
                return None
            
            activity = fragment.getParentActivity()
            if not activity:
                return None
            dialog_state = {"dialog": None, "dismissed": False}
            
            def create_and_show_dialog():
                try:
                    WebView = find_class("android.webkit.WebView")
                    Dialog = find_class("android.app.Dialog")
                    AndroidUtilities = find_class("org.telegram.messenger.AndroidUtilities")
                    ColorDrawable = find_class("android.graphics.drawable.ColorDrawable")
                    Theme = find_class("org.telegram.ui.ActionBar.Theme")
                    ViewGroup = find_class("android.view.ViewGroup")

                    dialog = Dialog(activity)
                    dialog.requestWindowFeature(1)

                    webview = WebView(activity)
                    webview.getSettings().setJavaScriptEnabled(True)
                    webview.setBackgroundColor(0)
                    webview.setLayerType(1, None)
                    webview.setVerticalScrollBarEnabled(False)
                    webview.setHorizontalScrollBarEnabled(False)
                    webview.loadDataWithBaseURL(None, _get_loading_html(), "text/html", "UTF-8", None)

                    size = AndroidUtilities.dp(120)
                    params = ViewGroup.LayoutParams(size, size)
                    dialog.setContentView(webview, params)

                    window = dialog.getWindow()
                    if window:
                        window.setBackgroundDrawable(ColorDrawable(0))
                        window.setDimAmount(0.4)                
                    dialog.show()
                    if window:
                        window.setLayout(size, size)
                    dialog_state["dialog"] = dialog
                    Runnable = find_class("java.lang.Runnable")
                    class DismissRunnable(dynamic_proxy(Runnable)):
                        def __init__(self, state):
                            super().__init__()
                            self.state = state
                        def run(self):
                            try:
                                if not self.state["dismissed"] and self.state["dialog"] and self.state["dialog"].isShowing():
                                    self.state["dialog"].dismiss()
                            except Exception as e:
                                log(f"[KPM] Error dismissing dialog: {e}")
                    AndroidUtilities.runOnUIThread(DismissRunnable(dialog_state), duration_ms)              
                except Exception as e:
                    log(f"[KPM] MD3 loading dialog creation failed: {e}")      
            def run_on_ui():
                try:
                    create_and_show_dialog()
                except Exception as e:
                    log(f"[KPM] Error in UI thread dialog creation: {e}")         
            run_on_ui_thread(run_on_ui)
            class DialogController:
                def __init__(self, state):
                    self.state = state
                
                def dismiss(self):
                    try:
                        self.state["dismissed"] = True
                        if self.state["dialog"] and self.state["dialog"].isShowing():
                            run_on_ui_thread(lambda: self.state["dialog"].dismiss() if self.state["dialog"] and self.state["dialog"].isShowing() else None)
                            return True
                        elif not self.state["dialog"]:
                            def try_dismiss_later():
                                try:
                                    if self.state["dialog"] and self.state["dialog"].isShowing():
                                        self.state["dialog"].dismiss()
                                except Exception:
                                    pass
                            run_on_ui_thread(try_dismiss_later, 100)
                            run_on_ui_thread(try_dismiss_later, 300)
                            run_on_ui_thread(try_dismiss_later, 600)
                        return True
                    except Exception:
                        return False
                
                def isShowing(self):
                    try:
                        if self.state["dismissed"]:
                            return False
                        return self.state["dialog"] and self.state["dialog"].isShowing()
                    except Exception:
                        return False
            
            return DialogController(dialog_state)

        except Exception as e:
            log(f"[KPM] MD3 loading animation failed: {e}")
            return None
    
    def _show_about_dialog(self):

        try:
            fragment = get_last_fragment()
            if not fragment:
                return
            
            context = fragment.getParentActivity()
            if not context:
                return
            
            plugin_count = len(self.plugins_list) if self.plugins_list else 0
            installed_count = len(self.list_installed_plugins())
            lang = _get_lang()
            
            bottom_sheet = BottomSheet(context, False, fragment.getResourceProvider())
            bottom_sheet.setApplyBottomPadding(False)
            bottom_sheet.setApplyTopPadding(False)
            bottom_sheet.fixNavigationBar(Theme.getColor(Theme.key_windowBackgroundWhite))
            
            linear_layout = LinearLayout(context)
            linear_layout.setOrientation(LinearLayout.VERTICAL)
            linear_layout.setClickable(True)
            
            frame_layout = FrameLayout(context)
            frame_layout.addView(linear_layout)
            
            scroll_view = NestedScrollView(context)
            scroll_view.addView(frame_layout)
            bottom_sheet.setCustomView(scroll_view)
            close_view = ImageView(context)
            close_view.setBackground(Theme.createSelectorDrawable(Theme.getColor(Theme.key_listSelector)))
            close_view.setColorFilter(Theme.getColor(Theme.key_sheet_other))
            close_view.setImageResource(R_tg.drawable.ic_layer_close)
            OnClickInterface = find_class("android.view.View$OnClickListener")
            OnClick = dynamic_proxy(OnClickInterface)
            class CloseClickImpl(OnClick):
                def __init__(self, bottom_sheet):
                    super().__init__()
                    self.bottom_sheet = bottom_sheet
                def onClick(self, v):
                    self.bottom_sheet.dismiss()
            close_view.setOnClickListener(CloseClickImpl(bottom_sheet))
            close_padding = AndroidUtilities.dp(8)
            close_view.setPadding(close_padding, close_padding, close_padding, close_padding)
            frame_layout.addView(close_view, LayoutHelper.createFrame(36, 36, Gravity.TOP | Gravity.END, 6, 8, 8, 0))

            sticker_image_view = BackupImageView(context)
            sticker_image_view.setRoundRadius(0)
            sticker_image_view.getImageReceiver().setCrossfadeWithOldImage(True)
            linear_layout.addView(sticker_image_view, LayoutHelper.createLinear(150, 150, Gravity.TOP | Gravity.CENTER_HORIZONTAL, 0, 27, 0, 0))
            self._load_sticker_async(sticker_image_view, "yurinators", 26, "about_dialog_sticker")
            
            title_text_view = SimpleTextView(context)
            title_text_view.setTypeface(AndroidUtilities.bold())
            title_text_view.setTextSize(20)
            title_text_view.setTextColor(Theme.getColor(Theme.key_dialogTextBlack))
            title_text = "Kangel Plugins Manager"
            
            title_text_view.setText(title_text)
            title_text_view.setGravity(Gravity.CENTER)
            linear_layout.addView(title_text_view, LayoutHelper.createLinear(-2, -2, Gravity.TOP | Gravity.CENTER_HORIZONTAL, 10, 27, 10, 0))

            version_text = TextView(context)
            version_text.setGravity(Gravity.CENTER)
            version_text.setText(f"{__version__} | 'Angel flight '")
            version_text.setTextColor(Theme.getColor(Theme.key_dialogTextGray3))
            version_text.setTextSize(TypedValue.COMPLEX_UNIT_DIP, 14)
            linear_layout.addView(version_text, LayoutHelper.createLinear(-1, -2, Gravity.TOP, 24, 4, 24, 0))

            info_text = TextView(context)
            info_text.setGravity(Gravity.CENTER)
            info_lines = [_tr("easter_egg_info")]
            info_text.setText("\n".join(info_lines))
            info_text.setTextColor(Theme.getColor(Theme.key_dialogTextBlack))
            info_text.setTextSize(TypedValue.COMPLEX_UNIT_DIP, 15)
            linear_layout.addView(info_text, LayoutHelper.createLinear(-1, -2, Gravity.TOP, 24, 20, 24, 20))
            
            bottom_sheet.show()
            log("[KPM] About dialog shown (easter egg)")
        except Exception as e:
            log(f"[KPM] Error showing about dialog: {e}")
            log(traceback.format_exc())

    def on_plugin_load(self):
        self.add_on_send_message_hook()
        self.add_deeplink_hook()
        self.add_drawer_menu_items()
        self.add_install_sheet_hook()
        self.add_plugins_activity_hook()
        self._setup_kpm_file_hook()
        self._setup_settings_header_hook()
        if self._pill_supported():
            self._register_kpm_pill()
        if self.get_setting("auto_update_on_start", False): run_on_queue(self.refresh_store)
        if self.get_setting("auto_update_installed", False): run_on_queue(self.update_installed_from_store)
        self.search_listener_hooks = None
        
        from base_plugin import MethodHook
        
        class InlineSearchBotHook(MethodHook):
            def __init__(self, plugin):
                self.plugin = plugin
            
            def before_hooked_method(self, param):
                try:
                    username = param.args[0]
                    query = param.args[1]
                    trigger = self.plugin.get_setting("inline_search_trigger", "kpm")
                    log(f"[KPM Inline] Bot hook: username={username}, trigger={trigger}")
                    if username and str(username).lower() == trigger.lower():
                        log(f"[KPM Inline] Match! Processing query: {query}")
                        param.setResult(None)
                        run_on_queue(lambda: self.plugin.process_inline_search(param.thisObject, query))
                except Exception as e:
                    log(f"[KPM] Inline search bot hook error: {e}")
        
        class InlineSearchHashtagHook(MethodHook):
            def __init__(self, plugin):
                self.plugin = plugin
            
            def before_hooked_method(self, param):
                try:
                    text = str(param.args[0])
                    trigger = "@" + self.plugin.get_setting("inline_search_trigger", "kpm")
                    log(f"[KPM Inline] Hashtag hook: text={text[:20]}, trigger={trigger}")
                    if text.lower().startswith(trigger.lower()):
                        log(f"[KPM Inline] Match! Processing")
                        param.setResult(None)
                        query = text[len(trigger):].strip()
                        run_on_queue(lambda: self.plugin.process_inline_search(param.thisObject, query))
                except Exception as e:
                    log(f"[KPM] Inline search hashtag hook error: {e}")
        
        MentionsAdapter = find_class("org.telegram.ui.Adapters.MentionsAdapter")
        if MentionsAdapter:
            self.hook_all_methods(MentionsAdapter.getClass(), "searchForContextBot", InlineSearchBotHook(self))
            self.hook_all_methods(MentionsAdapter.getClass(), "searchUsernameOrHashtag", InlineSearchHashtagHook(self))
            log("[KPM] Inline search hooks installed")

    def process_inline_search(self, adapter, query):
        try:
            query = str(query).lower().strip() if query else ""
            log(f"[KPM Inline] Searching for: '{query}', plugins count: {len(self.plugins_list)}")
            results = ArrayList()
            try:
                controller = PluginsController.getInstance()
                if controller:
                    pls = controller.plugins
                    for pid in pls.keySet().toArray():
                        try:
                            pl = pls.get(pid)
                            name = pl.getName() or ""
                            author = pl.getAuthor() or ""
                            desc = pl.getDescription() or ""
                            
                            match = False
                            if query:
                                if query in name.lower() or query in str(pid).lower():
                                    match = True
                                if not match and query in author.lower():
                                    match = True
                                if not match and desc and query in desc.lower():
                                    match = True
                            else:
                                match = True
                            
                            if match:
                                ver = pl.getVersion() or "1.0"
                                result = self._create_inline_result(
                                    f"local|{pid}",
                                    f"[Local] {name}",
                                    f"v{ver} | {author} | Tap to send"
                                )
                                if result:
                                    results.add(result)
                        except Exception as e:
                            log(f"[KPM] Error processing local plugin {pid}: {e}")
            except Exception as e:
                log(f"[KPM] Error getting local plugins: {e}")

            for pid, info in self.plugins_list.items():
                try:
                    if isinstance(info, dict):
                        name = info.get("name", "")
                        author = info.get("author", "")
                        desc = info.get("description", "")
                        
                        match = False
                        if query:
                            if query in name.lower() or query in pid.lower():
                                match = True
                            if not match and query in author.lower():
                                match = True
                            if not match and desc and query in desc.lower():
                                match = True
                        else:
                            match = True
                        
                        if match:
                            ver = info.get("version", "1.0")
                            result = self._create_inline_result(
                                f"remote|{pid}",
                                f"[Store] {name}",
                                f"v{ver} | {author} | Tap to download & send"
                            )
                            if result:
                                results.add(result)
                except Exception as e:
                    log(f"[KPM] Error processing store plugin {pid}: {e}")
            
            log(f"[KPM Inline] Found {results.size()} results")

            while results.size() > 50:
                results.remove(results.size() - 1)
            
            run_on_ui_thread(lambda: self._inject_inline_results(adapter, results), 50)
        except Exception as e:
            log(f"[KPM] Inline search error: {e}")
    
    def _create_inline_result(self, res_id, title, description):
        try:
            res = TLRPC.TL_botInlineResult()
            res.id = res_id
            res.type = "article"
            res.title = title
            res.description = description
            res.send_message = TLRPC.TL_botInlineMessageText()
            res.send_message.message = f".kpm_send {res_id}"
            res.send_message.no_webpage = True
            return res
        except Exception as e:
            log(f"[KPM] Error creating inline result: {e}")
            return None
    
    def _inject_inline_results(self, adapter, results):
        try:
            from hook_utils import set_private_field
            from java.lang import Boolean
            
            log(f"[KPM Inline] Injecting {results.size()} results")
            fake_bot = TLRPC.TL_user()
            fake_bot.id = 987654321
            fake_bot.username = self.get_setting("inline_search_trigger", "kpm")
            fake_bot.bot = True
            
            set_private_field(adapter, "foundContextBot", fake_bot)
            set_private_field(adapter, "searchResultBotContext", results)
            adapter.notifyDataSetChanged()
            
            delegate = get_private_field(adapter, "delegate")
            if delegate:
                try:
                    m = delegate.getClass().getDeclaredMethod("needChangePanelVisibility", Boolean.TYPE)
                    m.setAccessible(True)
                    m.invoke(delegate, True)
                    log("[KPM Inline] Panel visibility changed to True")
                except Exception as e:
                    log(f"[KPM Inline] Failed to change panel visibility: {e}")
            else:
                log("[KPM Inline] No delegate found")
        except Exception as e:
            log(f"[KPM] Error injecting inline results: {e}")

    def on_send_message_hook(self, account, params):
        from base_plugin import HookResult, HookStrategy
        try:
            if isinstance(params.message, str):
                text = params.message.strip()
                if text.startswith(".kpm_send "):
                    res_id = text.replace(".kpm_send ", "").strip()
                    if res_id.startswith("local|") or res_id.startswith("remote|"):
                        try:
                            log(f"[KPM InlineSend] Intercepted: res_id={res_id}, peer={getattr(params, 'peer', None)}")
                        except Exception:
                            pass
                        run_on_queue(lambda: self._process_inline_selection(res_id, params.peer))
                        return HookResult(strategy=HookStrategy.CANCEL)
        except Exception as e:
            log(f"[KPM] Error in on_send_message_hook: {e}")
        return HookResult()

    def on_plugin_unload(self):
        self.remove_hook("on_send_message_hook")
    
    def add_drawer_menu_items(self):
        try:
            if self.get_setting("show_drawer_menu", True):
                self.add_menu_item(MenuItemData(
                    menu_type=MenuItemType.DRAWER_MENU,
                    text="Plugin Manager",
                    icon="msg_addbot",
                    on_click=lambda ctx: self.open_settings_page()
                ))
                log("[KPM] Drawer menu items added")
            else:
                log("[KPM] Drawer menu disabled in settings")
        except Exception as e:
            log(f"[KPM] Error adding drawer menu: {e}")
    
    def open_settings_page(self):
        try:
            log(f"[KPM] open_settings_page: start id={self.id}")
            java_plugin = PluginsController.getInstance().plugins.get(self.id)
            fragment = get_last_fragment()
            log(f"[KPM] open_settings_page: java_plugin={java_plugin is not None} fragment={fragment is not None}")
            if java_plugin and fragment:
                run_on_ui_thread(lambda: fragment.presentFragment(PluginSettingsActivity(java_plugin)))
            else:
                log("[KPM] Could not open settings - plugin or fragment is None")
        except Exception as e:
            log(f"[KPM] Error opening settings: {e}")
            log(traceback.format_exc())
    
    def add_deeplink_hook(self):
        try:
            
            class KPMDeeplinkHook:
                def __init__(self, plugin):
                    self.plugin = plugin
                
                def before_hooked_method(self, param):
                    try:
                        if len(param.args) < 1:
                            return
                        intent = param.args[0]
                        if not intent or intent.getAction() != "android.intent.action.VIEW":
                            return
                        data = intent.getData()
                        if not data:
                            return
                        url = str(data)
                        
                        if url.startswith("tg://kpm_install"):
                            uri = Uri.parse(url)
                            plugin_id = uri.getQueryParameter("plugin")
                            if plugin_id:
                                log(f"[KPM] Deep link install: {plugin_id}")
                                run_on_queue(lambda: self.plugin._handle_deep_link_install(plugin_id))
                                param.setResult(None)
                        elif url.startswith("tg://kpm_list"):
                            log(f"[KPM] Deep link refresh list")
                            run_on_queue(lambda: self.plugin.refresh_store(force=True, md3_anim=False))
                            param.setResult(None)
                    except Exception as e:
                        log(f"[KPM] Error in deeplink hook: {e}")
                
                def after_hooked_method(self, param):
                    pass
            
            LaunchActivity = find_class("org.telegram.ui.LaunchActivity")
            if LaunchActivity:
                method = LaunchActivity.getClass().getDeclaredMethod("handleIntent",
                    find_class("android.content.Intent").getClass(),
                    find_class("java.lang.Boolean").TYPE,
                    find_class("java.lang.Boolean").TYPE,
                    find_class("java.lang.Boolean").TYPE,
                    find_class("org.telegram.messenger.browser.Browser$Progress").getClass(),
                    find_class("java.lang.Boolean").TYPE,
                    find_class("java.lang.Boolean").TYPE)
                method.setAccessible(True)
                self.hook_method(method, KPMDeeplinkHook(self))
                log("[KPM] Deeplink hook installed successfully")
        except Exception as e:
            log(f"[KPM] Error adding deeplink hook: {e}")
            log(traceback.format_exc())

    def _setup_kpm_file_hook(self):
        try:
            from java.lang import Class
            from java import jclass
            AndroidUtilitiesClass = Class.forName("org.telegram.messenger.AndroidUtilities")
            MessageObjectClass = Class.forName("org.telegram.messenger.MessageObject")
            ActivityClass = Class.forName("android.app.Activity")
            ResourcesProviderClass = Class.forName("org.telegram.ui.ActionBar.Theme$ResourcesProvider")
            open_for_view = AndroidUtilitiesClass.getDeclaredMethod(
                "openForView",
                MessageObjectClass,
                ActivityClass,
                ResourcesProviderClass,
                jclass("java.lang.Boolean").TYPE,
            )
            open_for_view.setAccessible(True)
            
            class OpenForViewHook:
                def __init__(hook_self):
                    hook_self._plugin_ref = weakref.ref(self)
                def before_hooked_method(hook_self, param):
                    try:
                        plugin = hook_self._plugin_ref()
                        if not plugin:
                            return
                        if len(param.args) >= 1:
                            msg = param.args[0]
                            if msg and hasattr(msg, "getDocumentName"):
                                name = msg.getDocumentName()
                                if name:
                                    name_lower = str(name).lower()
                                    if name_lower.endswith(".kpm"):
                                        plugin.log(f"Detected .kpm file click: {name}")
                                        plugin._handle_kpm_file_open(msg)
                                        param.setResult(False)
                    except Exception as e:
                        plugin.log(f"[KPM] File hook error: {e}")
            
            self.hook_method(open_for_view, OpenForViewHook())
            log("[KPM] KPM file hook installed")
        except Exception as e:
            log(f"[KPM] Error setting up KPM file hook: {e}")
    
    def _handle_kpm_file_open(self, message_object):
        try:
            from com.exteragram.messenger.plugins import PluginsController
            from org.telegram.messenger import MessagesController
            kpm_plugin_id = "kangel_plugins_manager"
            controller = PluginsController.getInstance()
            kpm_installed = False
            
            if controller and controller.plugins:
                if controller.plugins.containsKey(kpm_plugin_id):
                    kpm_installed = True
            
            if not kpm_installed:
                log(f"[KPM] KPM not installed, prompting user to install first...")
                self._show_kpm_required_dialog(message_object)
                return

            def process_file():
                try:
                    document = message_object.getDocument()
                    if not document:
                        log("[KPM] No document in message")
                        BulletinHelper.show_error("Cannot read file")
                        return

                    file_path = None

                    try:
                        from com.exteragram.messenger.utils.chats import ChatUtils
                        file_path = ChatUtils.getInstance().getPathToMessage(message_object)
                    except Exception as e:
                        log(f"[KPM] ChatUtils error: {e}")
                    
                    if not file_path:
                        file_path = self._get_message_file_path(message_object)
                    
                    log(f"[KPM] File path: {file_path}")
                    
                    if not file_path:
                        log("[KPM] Could not get file path from message")
                        BulletinHelper.show_error("Please wait for file to download")
                        return
                    
                    if not os.path.exists(file_path):
                        log(f"[KPM] File does not exist: {file_path}")
                        BulletinHelper.show_error(f"File not found: {file_path}")
                        return

                    from .sbroka import load_collection_file
                    from android_utils import run_on_ui_thread
                    try:
                        metadata, plugin_ids, collection = load_collection_file(file_path)
                        run_on_ui_thread(lambda: self._show_import_collection_designer(metadata, plugin_ids))
                    except Exception as e:
                        log(f"[KPM] Error loading collection: {e}")
                        BulletinHelper.show_error(f"Error: {e}")
                except Exception as e:
                    log(f"[KPM] Error processing KPM file: {e}")
                    BulletinHelper.show_error(f"Error: {e}")
            
            run_on_queue(process_file)
        except Exception as e:
            log(f"[KPM] Error handling KPM file open: {e}")
            BulletinHelper.show_error(f"Error: {e}")
    
    def _get_message_file_path(self, message_object):
        try:
            try:
                ChatUtils = jclass("com.exteragram.messenger.utils.chats.ChatUtils")
                path = ChatUtils.getInstance().getPathToMessage(message_object)
                if path:
                    return str(path)
            except:
                pass
            try:
                if hasattr(message_object, "messageOwner") and message_object.messageOwner:
                    doc = message_object.messageOwner.media and message_object.messageOwner.media.document
                    if doc and hasattr(doc, "localPath") and doc.localPath:
                        return str(doc.localPath)
            except:
                pass

            try:
                doc = message_object.getDocument()
                if doc and hasattr(doc, "getPathName"):
                    path = doc.getPathName()
                    if path:
                        return str(path)
            except:
                pass
            

            try:
                doc = message_object.getDocument()
                if doc and hasattr(doc, "getLocalPath"):
                    path = doc.getLocalPath()
                    if path:
                        return str(path)
            except:
                pass
            
            return None
        except:
            return None
    
    def _show_kpm_required_dialog(self, message_object):
        try:
            fragment = get_last_fragment()
            if not fragment:
                return
            
            from org.telegram.ui.ActionBar import AlertDialog
            from ui.alert import AlertDialogBuilder
            
            context = fragment.getParentActivity()
            if not context:
                return
            
            builder = AlertDialogBuilder(context)
            builder.set_title("KPM Required")
            builder.set_message("This file requires Kangel Plugins Manager to be installed first.\n\nWould you like to install it now?")
            builder.set_positive_button("Install KPM", lambda d, w: (
                d.dismiss(),
                self._install_kpm_from_file(message_object)
            ))
            builder.set_negative_button("Cancel", lambda d, w: d.dismiss())
            builder.show()
        except Exception as e:
            log(f"[KPM] Error showing KPM required dialog: {e}")
    
    def _install_kpm_from_file(self, message_object):
        try:
            self._handle_deep_link_install("kangel_plugins_manager")
        except Exception as e:
            log(f"[KPM] Error installing KPM: {e}")
            BulletinHelper.show_error("Failed to install KPM")
    
    def add_install_sheet_hook(self):
        try:
            from base_plugin import MethodHook

            class InstallDialogGuardHook(MethodHook):
                def __init__(self, plugin):
                    self.plugin = plugin

                def before_hooked_method(self, param):
                    try:
                        install_params = param.args[1]
                        if not install_params:
                            return
                        path_field = install_params.getClass().getDeclaredField("filePath")
                        path_field.setAccessible(True)
                        file_path = path_field.get(install_params)
                        if file_path and self.plugin._block_install_dialog_if_unsupported(str(file_path)):
                            param.setResult(None)
                        try:
                            file_path_str = str(file_path) if file_path else ""
                            filename = os.path.basename(file_path_str)
                            plugin_id_raw = filename.replace('.plugin', '').replace('.py', '').strip()
                            if plugin_id_raw.startswith('.temp_'):
                                plugin_id_raw = plugin_id_raw.replace('.temp_', '')
                            try:
                                with open(file_path_str, 'r', encoding='utf-8') as f:
                                    content = f.read()
                                id_match = re.search(r'__id__\s*=\s*["\']([^"\']+)["\']', content)
                                if id_match:
                                    plugin_id_raw = id_match.group(1)
                            except:
                                pass
                            if not self.plugin.plugins_list:
                                self.plugin.load_cache()
                            plugins_set = {k.lower() for k in self.plugin.plugins_list.keys()} if self.plugin.plugins_list else set()
                            is_trusted = plugin_id_raw.lower() in plugins_set
                            log(f"[KPM] InstallDialogGuardHook: {plugin_id_raw} in store.json={is_trusted}, trusted={is_trusted}")
                            install_params.trusted = is_trusted
                        except Exception as trust_check_e:
                            log(f"[KPM] Error checking trusted status: {trust_check_e}")
                            
                    except Exception as e:
                        log(f"[KPM] InstallDialogGuardHook failed: {e}")
            
            class InstallSheetHook(MethodHook):
                def __init__(self, plugin):
                    self.plugin = plugin
                
                def after_hooked_method(self, param):
                    def to_java_color(hex_val):
                        val = int(hex_val)
                        if val > 0x7FFFFFFF:
                            val -= 0x100000000
                        return val
                    
                    def modify_ui():
                        try:
                            sheet = param.thisObject
                            install_params = param.args[2]
                            
                            if not sheet or not install_params:
                                return
                            
                            file_path = None
                            try:
                                path_field = install_params.getClass().getDeclaredField("filePath")
                                path_field.setAccessible(True)
                                file_path = path_field.get(install_params)
                            except Exception as e:
                                log(f"[KPM] Error getting file path: {e}")
                                return
                            
                            if not file_path:
                                return
                            
                            file_path_str = str(file_path)
                            filename = os.path.basename(file_path_str)
                            plugin_id_from_file = None
                            try:
                                with open(file_path_str, 'r', encoding='utf-8') as f:
                                    content = f.read()
                                id_match = re.search(r'__id__\s*=\s*["\']([^"\']+)["\']', content)
                                if id_match:
                                    plugin_id_from_file = id_match.group(1)
                                    log(f"[KPM] Found __id__ in file: {plugin_id_from_file}")
                            except Exception as e:
                                log(f"[KPM] Error reading __id__ from file: {e}")
                            plugin_id_raw = plugin_id_from_file or filename.replace('.plugin', '').replace('.py', '').strip()
                            if plugin_id_raw.startswith('.temp_'):
                                plugin_id_raw = plugin_id_raw.replace('.temp_', '')
                            
                            log(f"[KPM] Looking up dependencies for: {plugin_id_raw}")
                            log(f"[KPM] Available plugins: {list(self.plugin.plugins_list.keys())[:10]}...")
                            dependencies = []
                            plugin_info = {}
                            if plugin_id_raw:
                                pid_lower = plugin_id_raw.lower()
                                matched = next((k for k in self.plugin.plugins_list if k.lower() == pid_lower), None)
                                log(f"[KPM] Match result for {pid_lower}: {matched}")
                                if matched:
                                    plugin_info = self.plugin.plugins_list[matched]
                                    try:
                                        if plugin_id_from_file and 'content' in locals():
                                            parsed_metadata = self.plugin.parse_plugin_metadata(content.encode("utf-8"))
                                            if isinstance(plugin_info, dict):
                                                plugin_info = dict(plugin_info)
                                                for meta_key in ("min_version", "app_version", "requirements"):
                                                    if parsed_metadata.get(meta_key):
                                                        plugin_info[meta_key] = parsed_metadata.get(meta_key)
                                    except Exception as e:
                                        log(f"[KPM] Failed to merge file metadata for {matched}: {e}")
                                    log(f"[KPM] Plugin info type: {type(plugin_info)}, content: {plugin_info}")
                                    if isinstance(plugin_info, dict):
                                        dependencies = plugin_info.get("dependencies", [])
                                    log(f"[KPM] Dependencies found: {dependencies}")
                            custom_view = None
                            try:
                                curr_cls = sheet.getClass()
                                while curr_cls is not None:
                                    try:
                                        f = curr_cls.getDeclaredField("customView")
                                        f.setAccessible(True)
                                        custom_view = f.get(sheet)
                                        if custom_view:
                                            break
                                    except:
                                        pass
                                    curr_cls = curr_cls.getSuperclass()
                            except:
                                pass
                            
                            if not custom_view:
                                try:
                                    f = sheet.getClass().getSuperclass().getDeclaredField("containerView")
                                    f.setAccessible(True)
                                    custom_view = f.get(sheet)
                                except:
                                    pass
                            
                            if not custom_view:
                                return

                            from android.util import TypedValue
                            ButtonWithCounterView = find_class("org.telegram.ui.Stories.recorder.ButtonWithCounterView")
                            ViewGroup = find_class("android.view.ViewGroup")
                            LinearLayout = find_class("android.widget.LinearLayout")
                            Theme = find_class("org.telegram.ui.ActionBar.Theme")
                            AndroidUtilities = find_class("org.telegram.messenger.AndroidUtilities")
                            LayoutHelper = find_class("org.telegram.ui.Components.LayoutHelper")

                            install_btn = None
                            parent_layout = None
                            
                            def scan_view(view, depth=0):
                                nonlocal install_btn, parent_layout
                                if not view:
                                    return
                                
                                if isinstance(view, ButtonWithCounterView):
                                    try:
                                        btn_text = str(view.getText())
                                        if btn_text and ("Install" in btn_text or "Установить" in btn_text or "Update" in btn_text or "Обновить" in btn_text):
                                            if not install_btn:  
                                                install_btn = view
                                                parent_layout = view.getParent()
                                                log(f"[KPM] Found install button: {btn_text}")
                                    except:
                                        if not install_btn:
                                            install_btn = view
                                            parent_layout = view.getParent()
                                
                                if isinstance(view, ViewGroup):
                                    count = view.getChildCount()
                                    for i in range(count):
                                        scan_view(view.getChildAt(i), depth + 1)
                            
                            scan_view(custom_view)
                            
                            try:
                                TextView = find_class("android.widget.TextView")
                                def apply_markdown_to_textviews(view):
                                    if not view:
                                        return
                                    if isinstance(view, TextView):
                                        try:
                                            text = str(view.getText())
                                            if text and ("@" in text or "**" in text or "*" in text or "[" in text):
                                                spannable, plain = _parse_markdown(text)
                                                if spannable:
                                                    view.setText(spannable)
                                                    try:
                                                        from android.text.method import LinkMovementMethod
                                                        view.setMovementMethod(LinkMovementMethod.getInstance())
                                                    except Exception:
                                                        pass
                                        except Exception:
                                            pass
                                    if isinstance(view, ViewGroup):
                                        for i in range(view.getChildCount()):
                                            apply_markdown_to_textviews(view.getChildAt(i))
                                apply_markdown_to_textviews(custom_view)
                            except Exception as e:
                                log(f"[KPM] Error applying markdown to install dialog: {e}")
                            
                            if not install_btn:
                                log("[KPM] Install button not found in dialog")
                                return
                            
                            if not parent_layout:
                                log("[KPM] Parent layout not found for install button")
                                return
                            
                            context = sheet.getContext()
                            resources_provider = None
                            try:
                                curr_cls = sheet.getClass()
                                while curr_cls is not None:
                                    try:
                                        m = curr_cls.getDeclaredMethod("getResourceProvider")
                                        m.setAccessible(True)
                                        resources_provider = m.invoke(sheet)
                                        if resources_provider:
                                            break
                                    except:
                                        pass
                                    curr_cls = curr_cls.getSuperclass()
                            except:
                                pass
                            
                            if dependencies:
                                log(f"[KPM] Adding dependencies button")
                                deps_btn = ButtonWithCounterView(context, True, resources_provider)
                                deps_btn.setText(_tr("install_dependencies"), False)
                                if resources_provider:
                                    deps_color = Theme.getColor(Theme.key_windowBackgroundWhiteBlueText, resources_provider)
                                    deps_pressed = Theme.getColor(Theme.key_windowBackgroundWhiteBlueText, resources_provider)
                                else:
                                    deps_color = Theme.getColor(Theme.key_windowBackgroundWhiteBlueText)
                                    deps_pressed = Theme.getColor(Theme.key_windowBackgroundWhiteBlueText)
                                deps_bg = Theme.createSimpleSelectorRoundRectDrawable(
                                    AndroidUtilities.dp(16),
                                    deps_color,
                                    deps_pressed
                                )
                                deps_btn.setBackground(deps_bg)
                                OnClickListener = find_class("android.view.View$OnClickListener")
                                class DepsClickListener(dynamic_proxy(OnClickListener)):
                                    def __init__(self, plugin_instance, deps_list):
                                        super().__init__()
                                        self.plugin_instance = plugin_instance
                                        self.deps_list = deps_list
                                    def onClick(self, v):
                                        run_on_queue(lambda: self._install_dependencies())
                                    def _install_dependencies(self):
                                        def show_dialog(title, message):
                                            try:
                                                fragment = get_last_fragment()
                                                if not fragment:
                                                    return
                                                activity = fragment.getParentActivity()
                                                if not activity:
                                                    return
                                                builder = AlertDialogBuilder(activity)
                                                builder.set_title(title)
                                                builder.set_message(message)
                                                builder.set_positive_button(_tr("ok_button"), lambda d, w: d.dismiss())
                                                builder.set_cancelable(True)
                                                builder.show()
                                            except Exception as e:
                                                log(f"[KPM] Error showing dialog: {e}")
                                        try:
                                            success_count = 0
                                            failed_count = 0
                                            failed_deps = []
                                            for dep_id in self.deps_list:
                                                try:
                                                    log(f"[KPM] Installing dependency: {dep_id}")
                                                    self.plugin_instance.install_plugin_by_id(dep_id, enable_after=True)
                                                    log(f"[KPM] Successfully installed dependency: {dep_id}")
                                                    success_count += 1
                                                except Exception as e:
                                                    failed_count += 1
                                                    failed_deps.append(dep_id)
                                                    log(f"[KPM] ERROR installing dependency {dep_id}: {e}")
                                            lang = _get_lang()
                                            result_lines = []
                                            for dep_id in self.deps_list:
                                                dep_name = self.plugin_instance.get_plugin_display_name(dep_id)
                                                display_name = dep_name if dep_name != dep_id else dep_id
                                                if dep_id in failed_deps:
                                                    result_lines.append(f"❌ {display_name}")
                                                else:
                                                    result_lines.append(f"✅ {display_name}")
                                            if failed_count == 0:
                                                final_title = _tr("dep_install_complete").format(success_count, len(self.deps_list))
                                                final_msg = "\n".join(result_lines)
                                            else:
                                                final_title = _tr("dep_install_error").format(success_count, len(self.deps_list), failed_count)
                                                final_msg = "\n".join(result_lines)
                                            run_on_ui_thread(lambda t=final_title, m=final_msg: show_dialog(t, m))
                                        except Exception as e:
                                            log(f"[KPM] Error in _install_dependencies: {e}")
                                            error_title = _tr("dep_error_title")
                                            error_msg = _tr("dep_error_msg").format(str(e)[:200])
                                            run_on_ui_thread(lambda t=error_title, m=error_msg: show_dialog(t, m))
                                deps_btn.setOnClickListener(DepsClickListener(self.plugin, dependencies))
                                try:
                                    install_btn.setText(_tr("install_button"), False)
                                except:
                                    pass
                                idx = -1
                                for i in range(parent_layout.getChildCount()):
                                    if parent_layout.getChildAt(i) == install_btn:
                                        idx = i
                                        break
                                if idx >= 0:
                                    try:
                                        old_lp = install_btn.getLayoutParams()
                                        if isinstance(old_lp, LinearLayout.LayoutParams):
                                            old_lp.topMargin = AndroidUtilities.dp(16)
                                            old_lp.bottomMargin = 0
                                            install_btn.setLayoutParams(old_lp)
                                            deps_lp = LinearLayout.LayoutParams(old_lp)
                                            deps_lp.topMargin = AndroidUtilities.dp(8)
                                            deps_lp.bottomMargin = AndroidUtilities.dp(8)
                                            parent_layout.addView(deps_btn, idx, deps_lp)
                                            log("[KPM] Dependencies button added to install dialog")
                                        else:
                                            parent_layout.addView(deps_btn, idx, LayoutHelper.createLinear(-1, 48, 0, 16, 28, 8, 0))
                                            log("[KPM] Dependencies button added to install dialog (fallback)")
                                    except Exception as e:
                                        log(f"[KPM] Error adding dependencies button: {e}")
                                        try:
                                            parent_layout.addView(deps_btn, idx, LayoutHelper.createLinear(-1, 48, 0, 16, 28, 8, 0))
                                            log("[KPM] Dependencies button added (simple fallback)")
                                        except Exception as e2:
                                            log(f"[KPM] Failed to add button: {e2}")

                            try:
                                plugin_id_check = plugin_id_raw or plugin_id_from_file
                                plugin_controller = PluginsController.getInstance()
                                plugin_in_store = False
                                try:
                                    if plugin_id_check and self.plugin.plugins_list:
                                        pid_lower = plugin_id_check.lower()
                                        plugin_in_store = any(k.lower() == pid_lower for k in self.plugin.plugins_list)
                                        log(f"[KPM] Check in store: id='{plugin_id_check}', found={plugin_in_store}")
                                except Exception:
                                    pass

                                if not plugin_in_store:
                                    check_info_text = TextView(context)
                                    check_info_text.setText(_tr("check_plugin_sub"))
                                    check_info_text.setTextSize(TypedValue.COMPLEX_UNIT_DIP, 12)
                                    try:
                                        check_info_text.setTextColor(Theme.getColor(Theme.key_dialogTextGray2))
                                    except Exception:
                                        pass

                                    try:
                                        check_info_lp = LinearLayout.LayoutParams(
                                            ViewGroup.LayoutParams.MATCH_PARENT,
                                            ViewGroup.LayoutParams.WRAP_CONTENT
                                        )
                                        check_info_lp.bottomMargin = AndroidUtilities.dp(4)
                                        parent_layout.addView(check_info_text, idx, check_info_lp)
                                    except Exception as e:
                                        log(f"[KPM] Failed to add check info text: {e}")
                                    
                                    check_btn = ButtonWithCounterView(context, True, resources_provider)
                                    check_btn.setText(_tr("check_plugin"), False)
                                    if resources_provider:
                                        check_color = Theme.getColor(Theme.key_windowBackgroundWhiteBlueText, resources_provider)
                                        check_pressed = Theme.getColor(Theme.key_windowBackgroundWhiteBlueText, resources_provider)
                                    else:
                                        check_color = Theme.getColor(Theme.key_windowBackgroundWhiteBlueText)
                                        check_pressed = Theme.getColor(Theme.key_windowBackgroundWhiteBlueText)
                                    check_bg = Theme.createSimpleSelectorRoundRectDrawable(
                                        AndroidUtilities.dp(16),
                                        check_color,
                                        check_pressed
                                    )
                                    check_btn.setBackground(check_bg)

                                    OnClickListener = find_class("android.view.View$OnClickListener")
                                    class CheckClickListener(dynamic_proxy(OnClickListener)):
                                        def onClick(self, v):
                                            try:
                                                from org.telegram.messenger import SendMessagesHelper, UserConfig
                                                AccountInstanceClass = find_class("org.telegram.messenger.AccountInstance")
                                                current_account = UserConfig.selectedAccount
                                                account_instance = AccountInstanceClass.getInstance(current_account)

                                                BOT_ID = 8683783103
                                                SendMessagesHelper.prepareSendingDocument(
                                                    account_instance,           
                                                    file_path_str,              
                                                    file_path_str,              
                                                    None,                      
                                                    None,                     
                                                    "application/octet-stream", 
                                                    BOT_ID,                     
                                                    None,                       
                                                    None,                       
                                                    None,                       
                                                    None,                       
                                                    None,                       
                                                    True,                      
                                                    0,                         
                                                    None,                      
                                                    None,                      
                                                    0,                          
                                                    False                      
                                                )

                                                from android.os import Bundle
                                                ChatActivity = find_class("org.telegram.ui.ChatActivity")
                                                if ChatActivity:
                                                    args = Bundle()
                                                    args.putLong("user_id", BOT_ID)
                                                    fragment = get_last_fragment()
                                                    if fragment:
                                                        fragment.presentFragment(ChatActivity(args))
                                                    
                                            except Exception as e:
                                                BulletinHelper.show_error(f"Ошибка отправки: {e}")

                                    check_btn.setOnClickListener(CheckClickListener())

                                    idx = -1
                                    for i in range(parent_layout.getChildCount()):
                                        if parent_layout.getChildAt(i) == install_btn:
                                            idx = i
                                            break
                                    if idx >= 0:
                                        try:
                                            install_lp = install_btn.getLayoutParams()
                                            if isinstance(install_lp, LinearLayout.LayoutParams):
                                                check_lp = LinearLayout.LayoutParams(install_lp)
                                                check_lp.topMargin = AndroidUtilities.dp(8)
                                                check_lp.bottomMargin = AndroidUtilities.dp(8)
                                                parent_layout.addView(check_btn, idx, check_lp)
                                                log("[KPM] Check plugin button added to install dialog")
                                            else:
                                                parent_layout.addView(check_btn, idx, LayoutHelper.createLinear(-1, 48, 0, 16, 28, 8, 0))
                                        except Exception as e:
                                            log(f"[KPM] Failed to add check button to install dialog: {e}")
                            except Exception as e:
                                log(f"[KPM] Error preparing check plugin button in install dialog: {e}")
                            
                            filename = os.path.basename(file_path_str)
                            plugin_id_raw = filename.replace(".plugin", "").replace(".py", "").strip()
                            if plugin_id_raw.startswith(".temp_"):
                                plugin_id_raw = plugin_id_raw.replace(".temp_", "")                  
                            status = None
                            if plugin_id_raw:
                                plugin_id_lower = plugin_id_raw.lower()
                                matched_key = next((k for k in self.plugin.plugins_list if k.lower() == plugin_id_lower), None)
                                if matched_key:
                                    plugin_info = self.plugin.plugins_list.get(matched_key)
                                    if isinstance(plugin_info, dict):
                                        status = plugin_info.get("status", "plugin")
                                if not status:
                                    try:
                                        with open(file_path_str, 'r', encoding='utf-8') as f:
                                            content = f.read()
                                        status_match = re.search(r'__status__\s*=\s*["\']([^"\']+)["\']', content)
                                        if status_match:
                                            status = status_match.group(1)
                                        else:
                                            if 'class.*BasePlugin' in content or '__id__' in content:
                                                id_match = re.search(r'__id__\s*=\s*["\']([^"\']+)["\']', content)
                                                if id_match:
                                                    file_id = id_match.group(1).lower()
                                                    for k, v in self.plugin.plugins_list.items():
                                                        if k.lower() == file_id:
                                                            if isinstance(v, dict):
                                                                status = v.get("status", "plugin")
                                                            break
                                    except Exception as e:
                                        log(f"[KPM] Error extracting status from file: {e}")
                                
                                if not status:
                                    status = "plugin"
                            
                            status_label = _status_label(status)
                            try:
                                from android.util import TypedValue
                                from android.view import Gravity
                                TextView = find_class("android.widget.TextView")
                                LL = find_class("android.widget.LinearLayout")
                                if custom_view and isinstance(custom_view, ViewGroup) and custom_view.getChildCount() > 0:
                                    main_layout = custom_view.getChildAt(0)
                                    if isinstance(main_layout, ViewGroup) and main_layout.getChildCount() > 0:
                                        main_layout = main_layout.getChildAt(0)
                                    
                                    if isinstance(main_layout, ViewGroup):
                                        ctx = main_layout.getContext()
                                        idx = 1
                                        source_badge = None
                                        for i in range(main_layout.getChildCount()):
                                            v = main_layout.getChildAt(i)
                                            if isinstance(v, LL) and v.getOrientation() == 0 and v.getChildCount() > 0:
                                                source_badge, idx = v, i
                                                break
                                        accent = Theme.getColor(Theme.key_windowBackgroundWhiteBlueHeader)
                                        dependencies = _normalize_requirements_list(plugin_info.get("dependencies", []) if isinstance(plugin_info, dict) else [])
                                        raw_requirements = _normalize_requirements_list(plugin_info.get("requirements", []) if isinstance(plugin_info, dict) else [])
                                        requirements = []
                                        for req in raw_requirements:
                                            req_lower = req.lower()
                                            matched_key = next((k for k in self.plugin.plugins_list if k.lower() == req_lower), None)
                                            req_status = "plugin"
                                            if matched_key:
                                                req_info = self.plugin.plugins_list.get(matched_key)
                                                if isinstance(req_info, dict):
                                                    req_status = req_info.get("status", "plugin")
                                            if req_status != "library":
                                                requirements.append(req)
                                        app_version = ""
                                        if isinstance(plugin_info, dict):
                                            app_version = plugin_info.get("app_version", "") or ""

                                        def _make_sheet_badge(text, color=None, alpha=0x15):
                                            badge = LL(ctx)
                                            badge.setOrientation(0)
                                            badge.setGravity(17)
                                            badge_color = color if color is not None else accent
                                            badge.setBackground(Theme.createRoundRectDrawable(
                                                AndroidUtilities.dp(20), AndroidUtilities.dp(20),
                                                (badge_color & 0x00FFFFFF) | (alpha << 24)
                                            ))
                                            badge.setPadding(AndroidUtilities.dp(14), AndroidUtilities.dp(6),
                                                             AndroidUtilities.dp(14), AndroidUtilities.dp(6))
                                            text_view = TextView(ctx)
                                            text_view.setText(text)
                                            text_view.setTypeface(AndroidUtilities.bold())
                                            text_view.setTextSize(1, 13.0)
                                            text_view.setTextColor(badge_color)
                                            badge.addView(text_view)
                                            return badge

                                        badge_views = [_make_sheet_badge(status_label)]
                                        dep_badge = ""
                                        app_badge = ""
                                        
                                        if source_badge:
                                           
                                            parent = source_badge.getParent()
                                            if parent and isinstance(parent, LL) and parent.getOrientation() == 0:
                                                for badge in reversed(badge_views):
                                                    parent.addView(badge, 0, LayoutHelper.createLinear(-2, -2, 0, 0, 0, 8, 0))
                                                log(f"[KPM] Install sheet badges added LEFT to existing row: {status_label}")
                                            else:
                                                row_cont = LL(ctx)
                                                row_cont.setOrientation(0)
                                                row_cont.setGravity(17)
                                                
                                                main_layout.removeView(source_badge)
                                                for badge in badge_views:
                                                    row_cont.addView(badge, LayoutHelper.createLinear(-2, -2, 0, 0, 0, 8, 0))
                                                row_cont.addView(source_badge, LayoutHelper.createLinear(-2, -2, 0, 0, 0, 0, 0))
                                                
                                                main_layout.addView(row_cont, idx, LayoutHelper.createLinear(-1, -2, 17, 0, 18, 0, 4))
                                                log(f"[KPM] Install sheet badges added LEFT in new row: {status_label}")
                                        else:
                                            pill_bg_color = Theme.getColor(Theme.key_dialogSearchBackground, resources_provider) if resources_provider else Theme.getColor(Theme.key_dialogSearchBackground)
                                            row_cont = LL(ctx)
                                            row_cont.setOrientation(0)
                                            row_cont.setGravity(Gravity.CENTER_VERTICAL)
                                            for badge_text in [status_label, dep_badge, app_badge]:
                                                if not badge_text:
                                                    continue
                                                pill_drawable = Theme.createRoundRectDrawable(AndroidUtilities.dp(8), pill_bg_color)
                                                pill_layout = LL(ctx)
                                                pill_layout.setOrientation(0)
                                                pill_layout.setGravity(Gravity.CENTER)
                                                pill_layout.setBackground(pill_drawable)
                                                pill_layout.setPadding(AndroidUtilities.dp(12), AndroidUtilities.dp(6),
                                                                       AndroidUtilities.dp(12), AndroidUtilities.dp(6))
                                                status_tv2 = TextView(ctx)
                                                if resources_provider:
                                                    status_tv2.setTextColor(Theme.getColor(Theme.key_dialogTextBlack, resources_provider))
                                                else:
                                                    status_tv2.setTextColor(Theme.getColor(Theme.key_dialogTextBlack))
                                                status_tv2.setTextSize(TypedValue.COMPLEX_UNIT_DIP, 13)
                                                status_tv2.setText(badge_text)
                                                status_tv2.setGravity(Gravity.CENTER)
                                                pill_layout.addView(status_tv2, LayoutHelper.createLinear(-2, -2, Gravity.CENTER_VERTICAL))
                                                row_cont.addView(pill_layout, LayoutHelper.createLinear(-2, -2, 0, 0, 0, 8, 0))
                                            main_layout.addView(row_cont, 0, LayoutHelper.createLinear(-2, -2, 0, 16, 8, 16, 8))
                                            log(f"[KPM] Install sheet top pills added (no source_badge): {status_label}")
                            except Exception as status_err:
                                log(f"[KPM] Could not add status badge: {status_err}")
                        
                        except Exception as e:
                            log(f"[KPM] Error modifying install sheet UI: {e}")
                            log(traceback.format_exc())
                    Handler = find_class("android.os.Handler")
                    Looper = find_class("android.os.Looper")
                    Runnable = find_class("java.lang.Runnable")
                    
                    class ModifyUIRunnable(dynamic_proxy(Runnable)):
                        def __init__(self):
                            super().__init__()
                        
                        def run(self):
                            modify_ui()
                    
                    handler = Handler(Looper.getMainLooper())
                    handler.postDelayed(ModifyUIRunnable(), 100)
            

            try:
                JavaClass = find_class("java.lang.Class")
                SheetClassJava = JavaClass.forName("com.exteragram.messenger.plugins.ui.components.InstallPluginBottomSheet")
            except Exception:
                SheetClassWrapper = find_class("com.exteragram.messenger.plugins.ui.components.InstallPluginBottomSheet")
                if SheetClassWrapper:
                    SheetClassJava = SheetClassWrapper.class_
                else:
                    log("[KPM] InstallPluginBottomSheet class not found")
                    return
            
            if not SheetClassJava:
                log("[KPM] InstallPluginBottomSheet class not found")
                return
            target_ctor = None
            constructors = SheetClassJava.getDeclaredConstructors()
            
            for ctor in constructors:
                params = ctor.getParameterTypes()
                if len(params) == 3:
                    p0 = params[0].getName()
                    p2 = params[2].getName()
                    if "BaseFragment" in p0 and "PluginInstallParams" in p2:
                        target_ctor = ctor
                        break
            
            if target_ctor:
                target_ctor.setAccessible(True)
                self.hook_method(target_ctor, InstallSheetHook(self))
                log("[KPM] Install sheet hook installed successfully")
            else:
                log("[KPM] InstallPluginBottomSheet constructor not found")
        
        except Exception as e:
            log(f"[KPM] Error adding install sheet hook: {e}")
            log(traceback.format_exc())
        try:
            PythonPluginsEngine = find_class("com.exteragram.messenger.plugins.PythonPluginsEngine")
            BaseFragment = find_class("org.telegram.ui.ActionBar.BaseFragment")
            PluginInstallParams = find_class("com.exteragram.messenger.plugins.ui.components.InstallPluginBottomSheet$PluginInstallParams")
            if PythonPluginsEngine and BaseFragment and PluginInstallParams:
                show_install_dialog = PythonPluginsEngine.getClass().getDeclaredMethod(
                    "showInstallDialog",
                    BaseFragment.getClass(),
                    PluginInstallParams.getClass()
                )
                show_install_dialog.setAccessible(True)
                self.hook_method(show_install_dialog, InstallDialogGuardHook(self))
                log("[KPM] Install dialog guard hook installed successfully")
        except Exception as e:
            log(f"[KPM] Error adding install dialog guard hook: {e}")
            log(traceback.format_exc())
    
    def add_plugins_activity_hook(self):
        try:
            from base_plugin import MethodHook
            
            class PluginsActivityHook(MethodHook):
                def __init__(self, plugin):
                    self.plugin = plugin
                
                def after_hooked_method(self, param):
                    try:
                        if not self.plugin.get_setting("show_add_button", True):
                            return
                        
                        activity = param.thisObject
                        action_bar = activity.actionBar
                        if not action_bar:
                            log("[KPM] ActionBar is None")
                            return
                        
                        menu = action_bar.menu
                        if not menu:
                            log("[KPM] Menu is None")
                            return     
                        try:
                            if hasattr(menu, 'ids') and menu.ids:
                                if 2 in [int(x) for x in menu.ids]:
                                    log("[KPM] Button '+' already exists (checked via ids)")
                                    return
                        except Exception as check_error:
                            log(f"[KPM] Could not check existing items: {check_error}")
                        
                        from org.telegram.messenger import R
                        
                        class AddButtonClickListener(dynamic_proxy(View.OnClickListener)):
                            def __init__(self, plugin_instance):
                                super().__init__()
                                self.plugin_instance = plugin_instance
                            
                            def onClick(self, v):
                                self.plugin_instance.open_install_dialog()
                        
                        class UpdateButtonClickListener(dynamic_proxy(View.OnClickListener)):
                            def __init__(self, plugin_instance):
                                super().__init__()
                                self.plugin_instance = plugin_instance
                            
                            def onClick(self, v):
                                self.plugin_instance.open_update_dialog()
                        
                        add_item = menu.addItem(2, R.drawable.msg_add)
                        add_item.setOnClickListener(AddButtonClickListener(self.plugin))
                        if self.plugin.get_setting("show_update_button", True):
                            update_item = menu.addItem(3, R.drawable.menu_browser_refresh)
                            update_item.setOnClickListener(UpdateButtonClickListener(self.plugin))
                            log("[KPM] Added '+' and update buttons to PluginsActivity menu")
                        else:
                            log("[KPM] Added '+' button to PluginsActivity menu (update button hidden by settings)")
                    except Exception as e:
                        log(f"[KPM] Error in PluginsActivity hook: {e}")
                        log(traceback.format_exc())
            
            PluginsActivity = find_class("com.exteragram.messenger.plugins.ui.PluginsActivity")
            if PluginsActivity:
                method = PluginsActivity.getClass().getDeclaredMethod("createView", find_class("android.content.Context").getClass())
                method.setAccessible(True)
                self.hook_method(method, PluginsActivityHook(self))
                log("[KPM] PluginsActivity hook installed successfully")
            else:
                log("[KPM] PluginsActivity class not found")
        except Exception as e:
            log(f"[KPM] Error adding PluginsActivity hook: {e}")
            log(traceback.format_exc())
    
    def _get_dependencies_from_file(self, file_path):
        try:
            if not os.path.exists(file_path):
                return []

            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()

            import re
            deps = []
            pattern = r'__dependencies__\s*=\s*\[(.*?)\]'
            match = re.search(pattern, content, re.DOTALL)
            if match:
                deps_str = match.group(1)
                for dep in deps_str.split(','):
                    dep = dep.strip().strip('"').strip("'")
                    if dep:
                        deps.append(dep)
                if deps:
                    log(f"[KPM] Found __dependencies__: {deps}")
                    return deps
            
            return []
        
        except Exception as e:
            log(f"[KPM] Error getting dependencies from file: {e}")
            return []

    def load_cache(self):
        try:
            if os.path.exists(self.cache_file):
                with open(self.cache_file, "r", encoding="utf-8") as f:
                    cache_data = json.load(f)
                    self.plugins_list = cache_data.get("plugins_list", {})
                    self.plugin_names_cache = cache_data.get("plugin_names", {})
                    cached_commit = cache_data.get("commit_sha", "")
                    log(f"[KPM] Loaded cache with {len(self.plugins_list)} plugins, {len(self.plugin_names_cache)} names (commit: {cached_commit[:7]})")
                    try:
                        self._build_trigram_index()
                    except Exception as e:
                        log(f"[KPM] Trigram index build (cache) failed: {e}")
        except Exception as e:
            log(f"[KPM] Error loading cache: {e}")

    def _normalize_search_text(self, text: str) -> str:
        try:
            if not text:
                return ""
            s = str(text).lower()
            s = re.sub(r"[^0-9a-zа-яё_\-\s]", " ", s, flags=re.IGNORECASE)
            s = re.sub(r"\s+", " ", s).strip()
            return s
        except Exception:
            return ""

    def _iter_trigrams(self, text: str):
        s = self._normalize_search_text(text)
        if not s:
            return []
        if len(s) < 3:
            return []
        return [s[i:i+3] for i in range(0, len(s) - 2)]

    def _build_trigram_index(self):
        self._trigram_index = {}
        self._search_text_cache = {}
        for pid, info in (self.plugins_list or {}).items():
            try:
                name = ""
                author = ""
                if isinstance(info, dict):
                    name = info.get("name") or ""
                    author = info.get("author") or ""
                text = f"{pid} {name} {author}"
                norm = self._normalize_search_text(text)
                self._search_text_cache[pid] = norm
                for tri in self._iter_trigrams(norm):
                    bucket = self._trigram_index.get(tri)
                    if bucket is None:
                        bucket = set()
                        self._trigram_index[tri] = bucket
                    bucket.add(pid)
            except Exception:
                continue
        log(f"[KPM] Trigram index built: {len(self._trigram_index)} keys")

    def _trigram_search(self, query: str, allowed_ids=None):
        q = self._normalize_search_text(query)
        if not q:
            return []
        if len(q) < 3:
            return []

        trigs = self._iter_trigrams(q)
        if not trigs:
            return []

        allowed_set = set(allowed_ids) if allowed_ids is not None else None
        scores = {}
        for tri in trigs:
            ids = self._trigram_index.get(tri)
            if not ids:
                continue
            if allowed_set is None:
                for pid in ids:
                    scores[pid] = scores.get(pid, 0) + 1
            else:
                for pid in ids:
                    if pid in allowed_set:
                        scores[pid] = scores.get(pid, 0) + 1

        if not scores:
            return []

        min_score = max(1, int(len(trigs) * 0.35))
        filtered = [(pid, sc) for pid, sc in scores.items() if sc >= min_score]
        filtered.sort(key=lambda x: (-x[1], x[0]))
        return [pid for pid, _ in filtered]

    def save_cache(self, commit_sha):
        try:
            cache_data = {
                "plugins_list": self.plugins_list,
                "plugin_names": self.plugin_names_cache,
                "commit_sha": commit_sha,
                "timestamp": int(time.time())
            }
            with open(self.cache_file, "w", encoding="utf-8") as f:
                json.dump(cache_data, f, ensure_ascii=False, indent=2)
            log(f"[KPM] Saved cache with {len(self.plugins_list)} plugins, {len(self.plugin_names_cache)} names (commit: {commit_sha[:7]})")
        except Exception as e:
            log(f"[KPM] Error saving cache: {e}")
    
    def clear_cache(self):
        try:
            if os.path.exists(self.cache_file):
                os.remove(self.cache_file)
                log("[KPM] Cache file deleted")
            
            self.plugins_list.clear()
            self.plugin_names_cache.clear()
            log("[KPM] Cache cleared from memory")
            
            run_on_ui_thread(lambda: BulletinHelper.show_error(_tr("cache_cleared")))
        except Exception as e:
            log(f"[KPM] Error clearing cache: {e}")
            run_on_ui_thread(lambda: BulletinHelper.show_error(f"Ошибка: {e}"))

    def get_latest_commit_sha(self):
        try:
            log(f"[KPM] Checking latest commit from GitHub API...")
            r = requests.get(self.github_api_url, timeout=10)
            if r.status_code == 200:
                commit_data = json.loads(r.text)
                sha = commit_data.get("sha", "")
                log(f"[KPM] Latest commit: {sha[:7]}")
                return sha
        except Exception as e:
            log(f"[KPM] Error getting commit SHA: {e}")
        return None

    def get_cached_commit_sha(self):
        try:
            if os.path.exists(self.cache_file):
                with open(self.cache_file, "r", encoding="utf-8") as f:
                    cache_data = json.load(f)
                    return cache_data.get("commit_sha", "")
        except Exception:
            pass
        return ""

    def _compare_versions(self, v1, v2):
        try:
            def parse_version(v):
                return [int(x) if x.isdigit() else x for x in re.split(r'(\d+)', str(v))]
            
            p1 = parse_version(v1)
            p2 = parse_version(v2)
            
            for a, b in zip(p1, p2):
                if a == b: continue
                if isinstance(a, int) and isinstance(b, int):
                    return 1 if a > b else -1
                return 1 if str(a) > str(b) else -1
            return len(p1) - len(p2)
        except Exception:
            return 0

    def is_cache_valid(self):
        cached_sha = self.get_cached_commit_sha()
        if not cached_sha:
            log("[KPM] No cached commit SHA, cache invalid")
            return False

        latest_sha = self.get_latest_commit_sha()
        if not latest_sha:
            log("[KPM] Could not get latest commit SHA, using cache")
            return True

        is_valid = cached_sha == latest_sha
        log(f"[KPM] Cache valid: {is_valid} (cached: {cached_sha[:7]}, latest: {latest_sha[:7]})")
        return is_valid

    def force_refresh_store(self):
        log("[KPM] Force refreshing store (clearing cache)...")
        self.plugins_list.clear()
        self.refresh_store(force=True)


    def refresh_store(self, force=False, has_bulletin=True, md3_anim=True):
        loading_dialog = None
        if md3_anim and (force or not self.is_cache_valid()):
            loading_dialog = self._show_md3_loading(4000)
        
        def do_refresh():
            if not force and self.is_cache_valid():
                log("[KPM] Cache is valid, skipping refresh")
                if has_bulletin:
                    run_on_ui_thread(lambda: BulletinHelper.show_error(_tr("cache_used").format(len(self.plugins_list))))
                return

            log("[KPM] Refreshing store from URLs...")

            for url in self.store_json_urls:
                try:
                    log(f"[KPM] Trying JSON URL: {url}")
                    r = requests.get(url, timeout=20)
                    log(f"[KPM] Response status: {r.status_code}")
                    if r.status_code == 200 and r.text:
                        try:
                            store_data = json.loads(r.text)
                        except Exception as e:
                            log(f"[KPM] JSON parse error: {e}")
                            continue
                        
                        if isinstance(store_data, dict):
                            normalized = {}
                            for pid, value in store_data.items():
                                if isinstance(value, str):
                                    normalized[pid] = {"url": value}
                                elif isinstance(value, dict):
                                    normalized[pid] = {
                                        "url": value.get("url", ""),
                                        "dependencies": value.get("dependencies", []),
                                        "requirements": _normalize_requirements_list(value.get("requirements", [])),
                                    }
                                   
                                    if value.get("name"):
                                        normalized[pid]["name"] = value.get("name")
                                    if value.get("version"):
                                        normalized[pid]["version"] = value.get("version")
                                    if value.get("icon"):
                                        normalized[pid]["icon"] = value.get("icon")
                                    if value.get("author"):
                                        normalized[pid]["author"] = value.get("author")
                                    if value.get("description"):
                                        normalized[pid]["description"] = value.get("description")
                                    if value.get("min_version"):
                                        normalized[pid]["min_version"] = value.get("min_version")
                                    if value.get("app_version"):
                                        normalized[pid]["app_version"] = value.get("app_version")
                                        if not normalized[pid].get("min_version"):
                                            normalized[pid]["min_version"] = _normalize_min_version(value.get("app_version"))
                                    normalized[pid]["status"] = value.get("status", "plugin")
                            

                            all_deps = set()
                            for plugin_info in normalized.values():
                                if isinstance(plugin_info, dict):
                                    deps = plugin_info.get("dependencies", [])
                                    all_deps.update(deps)

                            try:
                                self._all_deps_set = set(all_deps)
                            except Exception:
                                self._all_deps_set = set()
                            
                            libs = []
                            plugins = []
                            
                            for pid, plugin_info in normalized.items():
                                is_lib = pid in all_deps or "lib" in pid.lower()
                                if is_lib:
                                    libs.append((pid, plugin_info))
                                else:
                                    plugins.append((pid, plugin_info))
                            
                            self.plugins_list = normalized
                            try:
                                self._build_trigram_index()
                            except Exception as e:
                                log(f"[KPM] Trigram index build (refresh) failed: {e}")
                            
                            latest_sha = self.get_latest_commit_sha()
                            if latest_sha:
                                self.save_cache(latest_sha)
                            if loading_dialog:
                                try:
                                    run_on_ui_thread(lambda: loading_dialog.dismiss() if loading_dialog.isShowing() else None)
                                except Exception:
                                    pass
                            
                            if has_bulletin:
                                run_on_ui_thread(lambda: BulletinHelper.show_error(_tr("store_loaded").format(len(self.plugins_list))))
                            return
                except Exception as e:
                    log(f"[KPM] JSON store fetch fail {url}: {e}")
            if loading_dialog:
                try:
                    run_on_ui_thread(lambda: loading_dialog.dismiss() if loading_dialog.isShowing() else None)
                except Exception:
                    pass
            
            if has_bulletin:
                run_on_ui_thread(lambda: BulletinHelper.show_error(_tr("store_load_failed")))

        run_on_queue(do_refresh)

    def list_available_ids(self):
        if not self.plugins_list:
            self.load_cache()
        if not self.plugins_list:
            self.refresh_store()
        
        return list(self.plugins_list.keys())

    def parse_plugin_metadata(self, content):
        metadata = {
            "name": None,
            "description": None,
            "author": None,
            "version": None,
            "icon": None,
            "min_version": None,
            "app_version": None,
            "requirements": [],
        }
        try:
            lines = content.decode('utf-8', errors='ignore').split('\n')
            in_multiline = False
            multiline_key = None
            multiline_value = []
            
            for line in lines:
                line_stripped = line.strip()
                if in_multiline:
                    if '"""' in line_stripped:
                        multiline_value.append(line_stripped.split('"""')[0])
                        metadata[multiline_key] = '\n'.join(multiline_value).strip()
                        in_multiline = False
                        multiline_key = None
                        multiline_value = []
                    else:
                        multiline_value.append(line_stripped)
                    continue
                
                for key in ['__name__', '__description__', '__author__', '__version__', '__icon__', '__min_version__', '__app_version__', '__app_cersion__', '__requirements__']:
                    if line_stripped.startswith(key):
                        parts = line_stripped.split('=', 1)
                        if len(parts) == 2:
                            value = parts[1].strip()
                            metadata_key = key[2:-2]
                            if metadata_key == "app_cersion":
                                metadata_key = "app_version"
                            if value.startswith('"""'):
                                if value.count('"""') >= 2:
                                    parsed_value = value.strip('"').strip()
                                else:
                                    in_multiline = True
                                    multiline_key = metadata_key
                                    multiline_value = [value[3:]]
                                    continue
                            else:
                                parsed_value = value.strip('"').strip("'")
                            if metadata_key == "requirements":
                                metadata[metadata_key] = _normalize_requirements_list(parsed_value)
                            else:
                                metadata[metadata_key] = parsed_value
                        break
        except Exception as e:
            log(f"[KPM] Error parsing metadata: {e}")
        if metadata.get("app_version") and not metadata.get("min_version"):
            metadata["min_version"] = _normalize_min_version(metadata.get("app_version"))
        return metadata

    def get_plugin_display_name(self, plugin_id):
        if plugin_id in self.plugin_names_cache:
            return self.plugin_names_cache[plugin_id]
        
        if plugin_id not in self.plugins_list:
            return plugin_id
        
        try:
            plugin_info = self.plugins_list[plugin_id]

            if isinstance(plugin_info, dict) and plugin_info.get("name"):
                name = plugin_info.get("name")
                self.plugin_names_cache[plugin_id] = name
                return name

            url = plugin_info.get("url") if isinstance(plugin_info, dict) else plugin_info
            content = self.fetch_remote_bytes(url)
            metadata = self.parse_plugin_metadata(content)
            if metadata["name"]:
                self.plugin_names_cache[plugin_id] = metadata["name"]
                return metadata["name"]
        except Exception as e:
            log(f"[KPM] Error getting display name for {plugin_id}: {e}")
        
        self.plugin_names_cache[plugin_id] = plugin_id
        return plugin_id

    def open_update_dialog(self):
        loading_dialog = self._show_md3_loading(3000)
        
        def load_and_show():
            try:
                installed = self.list_installed_plugins()
                if not installed:
                    if loading_dialog:
                        try:
                            run_on_ui_thread(lambda: loading_dialog.dismiss() if loading_dialog.isShowing() else None)
                        except Exception:
                            pass
                    run_on_ui_thread(lambda: BulletinHelper.show_error(_tr("no_installed")))
                    return
                self.refresh_store(force=True, has_bulletin=False)
                
                updates = []
                display_names = {"d": {}, "ic": {}, "vers": {}}
                
                for pid in installed:
                    try:
                        plugin_info = self.plugins_list.get(pid)
                        if not plugin_info:
                            continue
                        
                        local_path = os.path.join(PLUGINS_DIR, f"{pid}.py")
                        if not os.path.exists(local_path):
                            continue
                        
                        local_bytes = self.read_file_bytes(local_path)
                        if not local_bytes:
                            continue
                        
                        local_metadata = self.parse_plugin_metadata(local_bytes)
                        local_version = local_metadata.get("version", "1.0")
                        
                        remote_version = str(plugin_info.get("version", "0"))
                        
                        if remote_version != local_version:
                            updates.append(pid)
                            display_names["d"][pid] = plugin_info.get("name", pid)
                            display_names["ic"][pid] = plugin_info.get("icon")
                            display_names["vers"][pid] = (local_version, remote_version)
                    except Exception as e:
                        log(f"[KPM] Error checking {pid}: {e}")
                        continue
                
                def show_dialog():
                    if loading_dialog:
                        try:
                            if loading_dialog.isShowing():
                                loading_dialog.dismiss()
                        except Exception:
                            pass
                    if not updates:
                        BulletinHelper.show_error(_tr("no_installed"))
                        return
                    self._show_plugin_list(_tr("update_plugins"), updates, display_names, KangelPluginsManagerPlugin.UPDATE)
                
                run_on_ui_thread(show_dialog)
            except Exception as e:
                log(f"[KPM] Error loading updates: {e}")
                if loading_dialog:
                    try:
                        run_on_ui_thread(lambda: loading_dialog.dismiss() if loading_dialog.isShowing() else None)
                    except Exception:
                        pass
        
        run_on_queue(load_and_show)

    def update_selected_plugins(self, plugin_ids, fn):
        updated = 0
        failed = 0
        first_incompatible = None
        for pid in plugin_ids:
            try:
                plugin_info = self.plugins_list.get(pid)
                if not plugin_info:
                    failed += 1
                    continue
                if not self._ensure_plugin_version_supported(pid, plugin_info, show_dialog=False):
                    if first_incompatible is None:
                        first_incompatible = self._get_plugin_version_state(pid, plugin_info)
                        first_incompatible = (pid, first_incompatible[0], first_incompatible[1])
                    failed += 1
                    continue
                
                url = plugin_info.get("url") if isinstance(plugin_info, dict) else plugin_info
                filename = f"{pid}.py"
                local_path = os.path.join(PLUGINS_DIR, filename)
                
                if not os.path.exists(local_path):
                    failed += 1
                    continue
                with open(local_path, "rb") as f:
                    local_bytes = f.read()
                if not local_bytes:
                    failed += 1
                    continue
                
                try:
                    remote = self.fetch_remote_bytes(url)
                    local_metadata = self.parse_plugin_metadata(local_bytes)
                    remote_metadata = self.parse_plugin_metadata(remote)
                    local_version = local_metadata.get("version", "0")
                    remote_version = remote_metadata.get("version", "0")
                except Exception:
                    failed += 1
                    continue
                
                if local_version != remote_version:
                    try:
                        tmp = local_path + ".tmp"
                        with open(tmp, "wb") as f:
                            f.write(remote)
                        if os.path.exists(local_path):
                            os.remove(local_path)
                        shutil.move(tmp, local_path)
                        updated += 1
                    except Exception:
                        failed += 1
                else:
                    log(f"[KPM] Plugin {pid} is already up to date")
            except Exception as e:
                log(f"[KPM] Error updating {pid}: {e}")
                failed += 1
        
        msg = _tr("updated_stats").format(updated, failed)
        fn()
        if first_incompatible is not None:
            run_on_ui_thread(lambda pid=first_incompatible[0], min_version=first_incompatible[1], client_version=first_incompatible[2]:
                self._show_requirements_dialog(pid, min_version, client_version))
        run_on_ui_thread(lambda: BulletinHelper.show_error(msg))
    
    def show_plugin_info_and_install(self, plugin_id, enable_after=False):
        def load_info():
            try:
                try:
                    self._mkstats_event("install_dialog_opened", 1)
                except Exception:
                    pass
                if not self.plugins_list:
                    log(f"[KPM] plugins_list is empty, refreshing store...")
                    self.refresh_store()
                
                plugin_info = self.plugins_list.get(plugin_id)
                if not plugin_info:
                    error_msg = f"Plugin {plugin_id} not found in store.json"
                    log(f"[KPM] {error_msg}")
                    run_on_ui_thread(lambda: BulletinHelper.show_error(error_msg))
                    return
                if not self._ensure_plugin_version_supported(plugin_id, plugin_info):
                    return
                
                url = plugin_info.get("url") if isinstance(plugin_info, dict) else plugin_info
                if not url:
                    error_msg = f"No URL found in store.json for plugin {plugin_id}"
                    log(f"[KPM] {error_msg}")
                    run_on_ui_thread(lambda: BulletinHelper.show_error(error_msg))
                    return
                
                log(f"[KPM] Installing {plugin_id} from store.json URL: {url}")
                
                info = self.get_plugin_full_info(plugin_id)
                if not info:
                    run_on_ui_thread(lambda: BulletinHelper.show_error(f"Failed to load {plugin_id}"))
                    return
                
                if not info.get('url') or info['url'] != url:
                    log(f"[KPM] Warning: URL mismatch, using store.json URL: {url}")
                    info['url'] = url
                
                dependencies = info.get("dependencies", [])
                
                def install_main_plugin():
                    try:
                        fragment = get_last_fragment()
                        if not fragment:
                            return
                        
                        temp_path = os.path.join(PLUGINS_DIR, f".temp_{plugin_id}.plugin")
                        error_msg = None
                        try:
                            plugin_url = info.get('url')
                            if not plugin_url:
                                raise Exception(f"No URL in info for {plugin_id}")
                            
                            log(f"[KPM] Downloading plugin from URL: {plugin_url}")
                            plugin_content = self.fetch_remote_bytes(plugin_url)
                            with open(temp_path, 'wb') as f:
                                f.write(plugin_content)
                            
                            PluginsController.getInstance().showInstallDialog(fragment, temp_path, True)
                            try:
                                self._mkstats_event("install_dialog_shown", 1)
                            except Exception:
                                pass
                            
                            log(f"[KPM] Opened Extera install dialog for {plugin_id}")
                        except Exception as download_error:
                            error_msg = str(download_error)
                            log(f"[KPM] Error downloading plugin for install dialog: {error_msg}")
                            if os.path.exists(temp_path):
                                try:
                                    os.remove(temp_path)
                                except:
                                    pass
                        
                        if error_msg:
                            run_on_ui_thread(lambda msg=error_msg: BulletinHelper.show_error(f"Error: {msg}"))
                    except Exception as e:
                        log(f"[KPM] Error showing Extera install dialog: {e}")
                        log(traceback.format_exc())
                
                if dependencies:
                    log(f"[KPM] Found {len(dependencies)} dependencies for {plugin_id}: {dependencies}")
                    def install_deps_then_open():
                        failed = []
                        for dep_id in dependencies:
                            try:
                                log(f"[KPM] Installing dependency: {dep_id}")
                                self.install_plugin_by_id(dep_id, enable_after=True)
                            except Exception as dep_e:
                                failed.append(dep_id)
                                log(f"[KPM] ERROR installing dependency {dep_id}: {dep_e}")
                        if failed:
                            try:
                                run_on_ui_thread(lambda: BulletinHelper.show_error(f"Deps failed: {', '.join(failed)}"))
                            except Exception:
                                pass
                        run_on_ui_thread(install_main_plugin)
                    run_on_queue(install_deps_then_open)
                else:
                    run_on_ui_thread(install_main_plugin)
                
            except Exception as e:
                log(f"[KPM] Error loading plugin info: {e}")
        
        run_on_queue(load_info)
    
    def _handle_deep_link_install(self, plugin_id):
        try:
            log(f"[KPM] Deep link: refreshing store for {plugin_id}")
            self.refresh_store(force=True, has_bulletin=False, md3_anim=False)
            
            plugin_info = self.plugins_list.get(plugin_id)
            if not plugin_info:
                run_on_ui_thread(lambda: BulletinHelper.show_error(_tr("plugin_not_found")))
                return
            if not self._ensure_plugin_version_supported(plugin_id, plugin_info):
                return
            run_on_ui_thread(lambda: self.show_plugin_info_and_install(plugin_id))
                
        except Exception as e:
            log(f"[KPM] Error in deep link install: {e}")
            run_on_ui_thread(lambda: BulletinHelper.show_error(f"Error: {e}"))
    
    def _show_requirements_dialog(self, plugin_id, min_version, client_version):
        def show_dialog():
            try:
                fragment = get_last_fragment()
                if not fragment:
                    return
                
                context = fragment.getParentActivity()
                if not context:
                    return
                
                lang = _get_lang()
                plugin_info = self.plugins_list.get(plugin_id, {})
                plugin_name = plugin_info.get("name", plugin_id) if isinstance(plugin_info, dict) else plugin_id
                
                bottom_sheet = BottomSheet(context, False, fragment.getResourceProvider())
                bottom_sheet.setApplyBottomPadding(False)
                bottom_sheet.setApplyTopPadding(False)
                bottom_sheet.fixNavigationBar(Theme.getColor(Theme.key_windowBackgroundWhite))
                
                linear_layout = LinearLayout(context)
                linear_layout.setOrientation(LinearLayout.VERTICAL)
                linear_layout.setClickable(True)
                
                frame_layout = FrameLayout(context)
                frame_layout.addView(linear_layout)
                
                scroll_view = NestedScrollView(context)
                scroll_view.addView(frame_layout)
                bottom_sheet.setCustomView(scroll_view)
                close_view = ImageView(context)
                close_view.setBackground(Theme.createSelectorDrawable(Theme.getColor(Theme.key_listSelector)))
                close_view.setColorFilter(Theme.getColor(Theme.key_sheet_other))
                close_view.setImageResource(R_tg.drawable.ic_layer_close)
                OnClickInterface = find_class("android.view.View$OnClickListener")
                OnClick = dynamic_proxy(OnClickInterface)
                class CloseClickImpl(OnClick):
                    def __init__(self, bottom_sheet):
                        super().__init__()
                        self.bottom_sheet = bottom_sheet
                    def onClick(self, v):
                        self.bottom_sheet.dismiss()
                close_view.setOnClickListener(CloseClickImpl(bottom_sheet))
                close_padding = AndroidUtilities.dp(8)
                close_view.setPadding(close_padding, close_padding, close_padding, close_padding)
                frame_layout.addView(close_view, LayoutHelper.createFrame(36, 36, Gravity.TOP | Gravity.END, 6, 8, 8, 0))
                sticker_image_view = BackupImageView(context)
                sticker_image_view.setRoundRadius(0)
                sticker_image_view.getImageReceiver().setCrossfadeWithOldImage(True)
                linear_layout.addView(sticker_image_view, LayoutHelper.createLinear(150, 150, Gravity.TOP | Gravity.CENTER_HORIZONTAL, 0, 27, 0, 0))
                self._load_sticker_async(sticker_image_view, "Rain_Stickers_Set", 16, "requirements_dialog_sticker")

                title_text_view = SimpleTextView(context)
                title_text_view.setTypeface(AndroidUtilities.bold())
                title_text_view.setTextSize(20)
                title_text_view.setTextColor(Theme.getColor(Theme.key_dialogTextBlack))
                title_text_view.setText(_tr("requirements_not_met"))
                title_text_view.setGravity(Gravity.CENTER)
                linear_layout.addView(title_text_view, LayoutHelper.createLinear(-2, -2, Gravity.TOP | Gravity.CENTER_HORIZONTAL, 10, 27, 10, 0))
                info_text = TextView(context)
                info_text.setGravity(Gravity.CENTER)
                version_info = _tr("version_requirements").format(min_version=min_version, client_version=client_version)
                spannable_info, plain_info = _parse_markdown(version_info, Theme.getColor(Theme.key_windowBackgroundWhiteBlueText))
                if spannable_info:
                    info_text.setText(spannable_info)
                    try:
                        from android.text.method import LinkMovementMethod
                        info_text.setMovementMethod(LinkMovementMethod.getInstance())
                    except Exception:
                        pass
                else:
                    info_text.setText(plain_info)
                info_text.setTextColor(Theme.getColor(Theme.key_dialogTextBlack))
                info_text.setTextSize(TypedValue.COMPLEX_UNIT_DIP, 15)
                linear_layout.addView(info_text, LayoutHelper.createLinear(-1, -2, Gravity.TOP, 24, 20, 24, 20))
                
                bottom_sheet.show()
                log("[KPM] Requirements dialog shown")
            except Exception as e:
                log(f"[KPM] Error showing requirements dialog: {e}")
        
        run_on_ui_thread(show_dialog)
    
    def _load_sticker_async(self, image_view, sticker_set_name, sticker_index, cache_key=None):
        def load_in_background():
            try:
                if cache_key and hasattr(self, '_sticker_cache') and cache_key in self._sticker_cache:
                    cached = self._sticker_cache[cache_key]
                    run_on_ui_thread(lambda: image_view.setImage(cached['location'], cached['size'], None, 0, cached['document']))
                    return
                
                current_account = 0
                try:
                    fragment = get_last_fragment()
                    if fragment:
                        current_account = fragment.getCurrentAccount()
                except:
                    pass
                
                media_controller = MediaDataController.getInstance(current_account)
                sticker_set = media_controller.getStickerSetByName(sticker_set_name)
                
                if sticker_set and sticker_set.documents and sticker_set.documents.size() > sticker_index:
                    sticker_document = sticker_set.documents.get(sticker_index)
                    image_location = ImageLocation.getForDocument(sticker_document)
                    if cache_key:
                        if not hasattr(self, '_sticker_cache'):
                            self._sticker_cache = {}
                        self._sticker_cache[cache_key] = {
                            'location': image_location,
                            'document': sticker_document,
                            'size': "150_150"
                        }
                    run_on_ui_thread(lambda: image_view.setImage(image_location, "150_150", None, 0, sticker_document))
                else:
                    try:
                        input_set = TLRPC.TL_inputStickerSetShortName()
                        input_set.short_name = sticker_set_name
                        
                        def on_set_response(result):
                            try:
                                if result and result.documents and result.documents.size() > sticker_index:
                                    doc = result.documents.get(sticker_index)
                                    img_loc = ImageLocation.getForDocument(doc)
                                    if cache_key:
                                        if not hasattr(self, '_sticker_cache'):
                                            self._sticker_cache = {}
                                        self._sticker_cache[cache_key] = {
                                            'location': img_loc,
                                            'document': doc,
                                            'size': "150_150"
                                        }
                                    
                                    run_on_ui_thread(lambda: image_view.setImage(img_loc, "150_150", None, 0, doc))
                            except:
                                pass
                        
                        class CallbackProxy(dynamic_proxy(Utilities.Callback)):
                            def __init__(self, fn):
                                super().__init__()
                                self._fn = fn
                            def run(self, arg):
                                try:
                                    self._fn(arg)
                                except:
                                    pass
                        
                        media_controller.getStickerSet(input_set, None, False, CallbackProxy(on_set_response))
                    except:
                        pass
            except:
                pass
        
        run_on_queue(load_in_background)
    
    def _mkstats_get_client_version(self) -> str:
        try:
            from org.telegram.messenger import BuildVars
            version = getattr(BuildVars, "BUILD_VERSION_STRING", None) or getattr(BuildVars, "BUILD_VERSION", None)
            if version:
                return str(version)
        except Exception:
            pass
        try:
            from org.telegram.messenger import BuildConfig as TgBuildConfig
            version = getattr(TgBuildConfig, "VERSION_NAME", None)
            if version:
                return str(version)
        except Exception:
            pass
        try:
            from com.radolyn.ayugram import BuildConfig as AyuBuildConfig
            version = getattr(AyuBuildConfig, "VERSION_NAME", None)
            if version:
                return str(version)
        except Exception:
            pass
        try:
            from com.exteragram.messenger import BuildConfig as ExBuildConfig
            version = getattr(ExBuildConfig, "VERSION_NAME", None)
            if version:
                return str(version)
        except Exception:
            pass
        try:
            from org.telegram.messenger import ApplicationLoader
            ctx = ApplicationLoader.applicationContext
            if ctx:
                pm = ctx.getPackageManager()
                pkg = ctx.getPackageName()
                info = pm.getPackageInfo(pkg, 0)
                version = getattr(info, "versionName", None) or getattr(info, "versionCode", None)
                if version:
                    return str(version)
        except Exception:
            pass
        return "unknown"

    def _mkstats_log(self, message: str) -> None:
        if hasattr(self, "log"):
            try:
                self.log(message)
            except Exception:
                pass

    def _mkstats_event(self, event: str, count: int = 1) -> None:
        return None

    def _get_temp_file(self, filename):
        try:
            from java.io import File
            d = File(ApplicationLoader.applicationContext.getExternalCacheDir(), "kpm_inline")
            if not d.exists():
                d.mkdirs()
            return File(d, filename)
        except Exception as e:
            log(f"[KPM] Error creating temp file: {e}")
            return None

    def _send_local_plugin(self, pid, peer_id):
        try:
            controller = PluginsController.getInstance()
            path = controller.getPluginPath(pid)
            pl = controller.plugins.get(pid)
            
            if not path or not os.path.exists(path):
                run_on_ui_thread(lambda: BulletinHelper.show_error("File not found"))
                return
            
            run_on_ui_thread(lambda: BulletinHelper.show_info(f"Preparing {pl.getName()}..."))
            
            try:
                ver = pl.getVersion() or "1.0"
                temp_file = self._get_temp_file(f"{pid}-{ver}.plugin")
                if not temp_file:
                    return
                
                with open(path, "rb") as src:
                    with open(temp_file.getAbsolutePath(), "wb") as dst:
                        dst.write(src.read())
                
                send_document(peer_id, temp_file.getAbsolutePath(), caption=f"Plugin: {pl.getName()}")
            except Exception as e:
                log(f"[KPM] Local send error: {e}")
        except Exception as e:
            log(f"[KPM] Send local plugin error: {e}")

    def _send_remote_plugin(self, key, peer_id):
        try:
            info = self.plugins_list.get(key)
            if not info:
                run_on_ui_thread(lambda: BulletinHelper.show_error("Not found"))
                return
            
            url = info.get("url") if isinstance(info, dict) else info
            name = info.get("name", key) if isinstance(info, dict) else key
            
            run_on_ui_thread(lambda: BulletinHelper.show_info(f"Downloading {name}..."))
            
            try:
                import requests
                try:
                    log(f"[KPM InlineSend] Download start: key={key}, url={url}, peer={peer_id}")
                except Exception:
                    pass
                resp = requests.get(url, timeout=20)
                if resp.status_code != 200:
                    run_on_ui_thread(lambda: BulletinHelper.show_error("Network error"))
                    return
                
                ver = info.get("version", "1.0") if isinstance(info, dict) else "1.0"
                temp_file = self._get_temp_file(f"{name}-{ver}.plugin")
                if not temp_file:
                    return
                
                with open(temp_file.getAbsolutePath(), "wb") as dst:
                    dst.write(resp.content)
                
                send_document(peer_id, temp_file.getAbsolutePath(), caption=f"Plugin: {name}")
            except Exception as e:
                log(f"[KPM] Remote send error: {e}")
                try:
                    run_on_ui_thread(lambda: BulletinHelper.show_error(str(e)))
                except Exception:
                    pass
        except Exception as e:
            log(f"[KPM] Send remote plugin error: {e}")

    def _process_inline_selection(self, result_id, peer_id):
        try:
            try:
                log(f"[KPM InlineSend] Selection: result_id={result_id}, peer={peer_id}")
            except Exception:
                pass
            type_str, pid = result_id.split("|", 1)
            if type_str == "local":
                self._send_local_plugin(pid, peer_id)
            elif type_str == "remote":
                self._send_remote_plugin(pid, peer_id)
        except Exception as e:
            log(f"[KPM] Selection error: {e}")

    def __init__(self):
        super().__init__()
        global _kpm_instance
        _kpm_instance = self
        self.store_json_urls = [
            "https://raw.githubusercontent.com/KangelPlugins/Plugins-Store/refs/heads/main/store.json",
            "https://raw.githubusercontent.com/KangelPlugins/Plugins-Store/main/store.json",
        ]
        self.github_api_url = "https://api.github.com/repos/KangelPlugins/Plugins-Store/commits/main"
        self.cache_file = os.path.join(PLUGINS_DIR, ".kpm_cache.json")
        self.plugins_list = {}
        self.plugin_names_cache = {}
        self._install_dialog_views_cache = {}
        self._sticker_cache = {}  
        self._trigram_index = {}
        self._search_text_cache = {}
        self._active_pills = weakref.WeakSet()
        self._pill_registered = False
        self._pill_hooks_installed = False
        self._pill_tag_key = jint(0x4B504D)
        self.PillRegistry = find_class("com.exteragram.messenger.pillstack.core.PillRegistry")
        self.PillInfo = find_class("com.exteragram.messenger.pillstack.core.PillRegistry$PillInfo")
        self.PillCreator = find_class("com.exteragram.messenger.pillstack.core.PillRegistry$PillCreator")
        self.PillStackConfig = find_class("com.exteragram.messenger.pillstack.core.PillStackConfig")
        self.WeatherPill = find_class("com.exteragram.messenger.pillstack.ui.pills.weather.WeatherPill")
        self.auto_update = True
        self.plugins_dir = PLUGINS_DIR
        self.cache_file = os.path.join(self.plugins_dir, ".kpm_cache.json")
        self.load_cache()

    def get_plugin_full_info(self, plugin_id):
        try:
            plugin_info = self.plugins_list.get(plugin_id)
            if not plugin_info:
                log(f"[KPM] Plugin {plugin_id} not found in plugins_list")
                return None
            url = plugin_info.get("url") if isinstance(plugin_info, dict) else plugin_info
            filename = f"{plugin_id}.py"
            local_path = os.path.join(PLUGINS_DIR, filename)
            
            if os.path.exists(local_path):
                with open(local_path, "rb") as f:
                    content = f.read()
            else:
                content = self.fetch_remote_bytes(url)
            
            metadata = self.parse_plugin_metadata(content)
            
            metadata["plugin_id"] = plugin_id
            metadata["url"] = url  
            metadata["dependencies"] = plugin_info.get("dependencies", []) if isinstance(plugin_info, dict) else []
            metadata["requirements"] = _normalize_requirements_list(plugin_info.get("requirements", [])) if isinstance(plugin_info, dict) else _normalize_requirements_list(metadata.get("requirements"))
            metadata["status"] = plugin_info.get("status", "plugin") if isinstance(plugin_info, dict) else "plugin"
            
            if isinstance(plugin_info, dict):
                if plugin_info.get("name") and not metadata.get("name"):
                    metadata["name"] = plugin_info.get("name")
                if plugin_info.get("version") and not metadata.get("version"):
                    metadata["version"] = plugin_info.get("version")
                if plugin_info.get("author") and not metadata.get("author"):
                    metadata["author"] = plugin_info.get("author")
                if plugin_info.get("description") and not metadata.get("description"):
                    metadata["description"] = plugin_info.get("description")
                if plugin_info.get("icon") and not metadata.get("icon"):
                    metadata["icon"] = plugin_info.get("icon")
                if plugin_info.get("min_version") and not metadata.get("min_version"):
                    metadata["min_version"] = plugin_info.get("min_version")
                if plugin_info.get("app_version") and not metadata.get("app_version"):
                    metadata["app_version"] = plugin_info.get("app_version")
                if plugin_info.get("requirements") and not metadata.get("requirements"):
                    metadata["requirements"] = _normalize_requirements_list(plugin_info.get("requirements"))

            if metadata.get("app_version") and not metadata.get("min_version"):
                metadata["min_version"] = _normalize_min_version(metadata.get("app_version"))
            
            if not metadata["name"]:
                metadata["name"] = plugin_id
            if not metadata["description"]:
                metadata["description"] = _tr("no_description")
            if not metadata["author"]:
                metadata["author"] = "Unknown"
            if not metadata["version"]:
                metadata["version"] = "1.0"
            
            return metadata
        except Exception as e:
            log(f"[KPM] Error getting full info: {e}")
            return None
    

    def open_install_dialog(self):
        fragment = get_last_fragment()
        if not fragment:
            return
        attempts = [0]
        loading_dialog = self._show_md3_loading(5000)
        
        def load_and_show():
            try:
                ids = self.list_available_ids()
                if not ids:
                    if attempts[0] < 3:
                        attempts[0] += 1
                        try:
                            self.refresh_store(force=True, has_bulletin=False)
                        except Exception:
                            pass
                        try:
                            import time
                            time.sleep(1.0)
                        except Exception:
                            pass
                        run_on_queue(load_and_show)
                        return
                    if loading_dialog:
                        try:
                            run_on_ui_thread(lambda: loading_dialog.dismiss() if loading_dialog.isShowing() else None)
                        except Exception:
                            pass
                    run_on_ui_thread(lambda: BulletinHelper.show_error(_tr("list_empty")))
                    return
                
                log(f"[KPM] Loading display names for {len(ids)} plugins from cache...")
                display_names = {}
                
                for pid in ids:
                    if pid in self.plugin_names_cache:
                        display_names[pid] = self.plugin_names_cache[pid]
                    else:
                        display_names[pid] = pid
                
                log(f"[KPM] Loaded {len(display_names)} display names from cache")
                
                def create_dialog():
                    try:
                        if loading_dialog:
                            try:
                                if loading_dialog.isShowing():
                                    loading_dialog.dismiss()
                            except Exception:
                                pass
                        current_fragment = get_last_fragment()
                        if not current_fragment:
                            log("[KPM] Fragment is None when creating install dialog")
                            return
                        self._show_plugin_list(f"{_tr('install_title')} ({len(ids)})", ids, display_names)
                    
                    except Exception as e:
                        log(f"[KPM] Error creating install dialog: {e}")
                
                run_on_ui_thread(create_dialog)
                
                def update_names_in_background():
                    try:
                        failed_pids = []
                        for pid in ids:
                            if pid not in self.plugin_names_cache:
                                try:
                                    name = self.get_plugin_display_name(pid)
                                    if name != pid:
                                        display_names[pid] = name
                                        log(f"[KPM] Updated name for {pid}: {name}")
                                except Exception as e:
                                    log(f"[KPM] Error updating name for {pid}: {e}")
                                    failed_pids.append(pid)
                    except Exception as e:
                        log(f"[KPM] Error in background name update: {e}")
                
                run_on_queue(update_names_in_background)
                
            except Exception as e:
                log(f"[KPM] Error loading plugins: {e}")
                if loading_dialog:
                    try:
                        run_on_ui_thread(lambda: loading_dialog.dismiss() if loading_dialog.isShowing() else None)
                    except Exception:
                        pass
                run_on_ui_thread(lambda: BulletinHelper.show_error(f"Ошибка: {e}"))
        
        run_on_queue(load_and_show)
    
    def _show_plugin_list(self, title, ids, display_names, type = 0):
        current_fragment = get_last_fragment()
        delegate = self.PluginListFragment(self, title, ids, display_names, type)
        fragment = UniversalFragment(delegate)
        current_fragment.presentFragment(fragment)
        fragment.setTitle(title, False, 0)
        base_title = title
        from java.lang import Boolean, Integer
        from org.telegram.ui.ActionBar import (ActionBar, ActionBarMenuItem,
                                               BackDrawable)
        
        if self.search_listener_hooks:
            for h in self.search_listener_hooks:
                self.unhook_method(h)
        self.search_listener_hooks = []
        id = 0
        def update_query(query):
            if query == delegate.search_query:
                return
            nonlocal id
            id += 1
            delegate.search_query = query
            def update(cid):
                nonlocal id
                if id != cid:
                    return
                delegate.adapter.update(True)
            
            run_on_ui_thread(lambda: update(id), 500)
            
        class SearchCollapseHook(MethodHook):
            def after_hooked_method(self, param):
                if param.thisObject != item or param.args[0] == True:
                    return
                param.setResult(None)
                update_query(None)
                
        hook = self.hook_method(ActionBarMenuItem.getClass().getDeclaredMethod("toggleSearch", Boolean.TYPE), SearchCollapseHook())
        self.search_listener_hooks.append(hook)

        class SearchTextChangedHook(MethodHook):
            def before_hooked_method(self, param):
                if param.thisObject != listener:
                    return
                search_query: str = search_field.getText().toString()
                if search_query.isspace():
                    search_query = None
                update_query(search_query)
        
        item = fragment.getActionBar().createMenu().addItem(0, R_tg.drawable.ic_ab_search).setIsSearchField(True)
        search_field = item.getSearchField()
        listener = get_private_field(search_field, "mListeners").get(0)
        from java.lang import CharSequence
        hook = self.hook_method(listener.getClass().getDeclaredMethod("onTextChanged", CharSequence, Integer.TYPE, Integer.TYPE, Integer.TYPE), SearchTextChangedHook())
        self.search_listener_hooks.append(hook)  

        try:
            from android_utils import OnClickListener
            def show_sort_dialog(*_):
                try:
                    items = [
                        _tr("sort_none"),
                        _tr("sort_az"),
                        _tr("sort_za"),
                        _tr("sort_author_az"),
                        _tr("sort_author_za"),
                    ]
                    current = int(self.get_setting("plugins_sort_mode", 0) or 0)

                    def on_pick(bld, which):
                        try:
                            self.set_setting("plugins_sort_mode", int(which), reload_settings=False)
                        except Exception:
                            self.set_setting("plugins_sort_mode", int(which))
                        try:
                            delegate.adapter.update(True)
                        except Exception:
                            pass
                        try:
                            bld.dismiss()
                        except Exception:
                            pass

                    builder = AlertDialogBuilder(fragment.getParentActivity())
                    builder.set_title(_tr("plugins_sort"))
                    builder.set_items(items, on_pick)
                    builder.set_negative_button(_tr("cancel"), lambda b, w: b.dismiss())
                    builder.show()
                except Exception as e:
                    log(f"[KPM] sort dialog error: {e}")

            fragment.getActionBar().createMenu().addItem(5, R_tg.drawable.menu_sort_value).setOnClickListener(OnClickListener(show_sort_dialog))
        except Exception as e:
            log(f"[KPM] Failed to add sort button: {e}")

        try:
            from android_utils import OnClickListener

            statuses = [
                ("*", _tr("filter_all")),
                ("customization", _tr("status_customization")),
                ("utilities", _tr("status_utilities")),
                ("informational", _tr("status_informational")),
                ("messages", _tr("status_messages")),
                ("fun", _tr("status_fun")),
                ("library", _tr("status_library")),
            ]

            action_bar = fragment.getActionBar()
            title_tv = None
            try:
                title_tv = action_bar.getTitleTextView()
            except Exception:
                title_tv = None

            def _label_for(key):
                try:
                    for k, l in statuses:
                        if k == key:
                            return l
                except Exception:
                    pass
                return _tr("filter_all")

            def _apply_header_label(key):
                try:
                    label = _label_for(key)
                    txt = f"{base_title}"
                    if title_tv is not None:
                        try:
                            title_tv.setLeftDrawable(R_tg.drawable.menu_filter)
                        except Exception:
                            pass
                        try:
                            try:
                                title_tv.setLeftDrawableOutside(True)
                            except Exception:
                                pass
                            title_tv.setGravity(Gravity.CENTER)
                        except Exception:
                            try:
                                title_tv.setGravity(Gravity.CENTER)
                            except Exception:
                                pass
                        try:
                            title_tv.setDrawablePadding(AndroidUtilities.dp(4.0))
                        except Exception:
                            pass
                        title_tv.setText(txt)
                        try:
                            action_bar.setSubtitle(str(label))
                        except Exception:
                            pass
                        try:
                            stv = action_bar.getSubtitleTextView()
                            if stv is not None:
                                try:
                                    stv.setGravity(Gravity.CENTER)
                                except Exception:
                                    pass
                                try:
                                    stv.setLayoutParams(LayoutHelper.createFrame(-1, -2, Gravity.TOP | Gravity.CENTER_HORIZONTAL))
                                except Exception:
                                    pass
                        except Exception:
                            pass
                    else:
                        action_bar.setTitle(txt)
                        try:
                            action_bar.setSubtitle(str(label))
                        except Exception:
                            pass
                        try:
                            stv = action_bar.getSubtitleTextView()
                            if stv is not None:
                                try:
                                    stv.setGravity(Gravity.CENTER)
                                except Exception:
                                    pass
                                try:
                                    stv.setLayoutParams(LayoutHelper.createFrame(-1, -2, Gravity.TOP | Gravity.CENTER_HORIZONTAL))
                                except Exception:
                                    pass
                        except Exception:
                            pass
                except Exception:
                    pass

            def show_filter_dialog(*_):
                try:
                    labels = [x[1] for x in statuses]
                    current = str(self.get_setting("plugins_status_filter", "*") or "*")

                    def on_pick(bld, which):
                        try:
                            key = statuses[int(which)][0]
                            try:
                                self.set_setting("plugins_status_filter", key, reload_settings=False)
                            except Exception:
                                self.set_setting("plugins_status_filter", key)
                            try:
                                self._mkstats_event("filter_status_changed", 1)
                            except Exception:
                                pass
                            _apply_header_label(key)
                            try:
                                delegate.adapter.update(True)
                            except Exception:
                                pass
                            try:
                                bld.dismiss()
                            except Exception:
                                pass
                        except Exception:
                            pass

                    builder = AlertDialogBuilder(fragment.getParentActivity())
                    builder.set_title(_tr("filter_status"))
                    builder.set_items(labels, on_pick)
                    builder.set_negative_button(_tr("cancel"), lambda b, w: b.dismiss())
                    builder.show()
                except Exception as e:
                    log(f"[KPM] filter dialog error: {e}")

            if title_tv is not None:
                try:
                    title_tv.setOnClickListener(OnClickListener(show_filter_dialog))
                except Exception:
                    pass
            else:
                try:
                    action_bar.setOnClickListener(OnClickListener(show_filter_dialog))
                except Exception:
                    pass

            try:
                current = str(self.get_setting("plugins_status_filter", "*") or "*")
            except Exception:
                current = "*"
            _apply_header_label(current)
        except Exception as e:
            log(f"[KPM] Failed to setup filter title: {e}")

    INSTALL = 0
    UPDATE = 1
     
    class PluginListFragment(dynamic_proxy(UniversalFragment.UniversalFragmentDelegate)):
        
        class Callback2(dynamic_proxy(Utilities.Callback2)):
            def __init__(self, fn):
                super().__init__()
                self.fn = fn
            
            def run(self, *args):
                self.fn(*args)
    
        class Callback5(dynamic_proxy(Utilities.Callback5)):
            def __init__(self, fn):
                super().__init__()
                self.fn = fn
            
            def run(self, *args):
                self.fn(*args)
        
        class Callback5Return(dynamic_proxy(Utilities.Callback5Return)):
            def __init__(self, fn):
                super().__init__()
                self.fn = fn
            
            def run(self, *args):
                return self.fn(*args)
        
        class PluginCellDelegate(dynamic_proxy(PluginCellDelegate)):
            def __init__(self, id, outer: "KangelPluginsManagerPlugin.PluginListFragment"):
                super().__init__()
                self.id = id
                self.outer = outer
                
            def canOpenInExternalApp(self):
                return False

            def deletePlugin(self):
                return None

            def openInExternalApp(self):
                pass

            def openPluginSettings(self):
                pass

            def pinPlugin(self,view):
                pass

            def sharePlugin(self):
                if not self.id:
                    return

                fragment = get_last_fragment()
                if not fragment:
                    return

                plugin_id = self.id
                link = f"tg://kpm_install?plugin={plugin_id}"

                def copy_link():
                    AndroidUtilities.addToClipboard(link)
                    BulletinHelper.show_copied_to_clipboard()

                def view_raw_url():
                    try:
                        try:
                            self.outer.pl._mkstats_event("raw_opened", 1)
                        except Exception:
                            pass
                        plugin_info = self.outer.pl.plugins_list.get(plugin_id)
                        if not plugin_info:
                            run_on_ui_thread(lambda: BulletinHelper.show_error(_tr("list_empty")))
                            return
                        url = plugin_info.get("url") if isinstance(plugin_info, dict) else plugin_info
                        if not url:
                            run_on_ui_thread(lambda: BulletinHelper.show_error(_tr("error_download").format("No URL")))
                            return

                        def show_dialog():
                            try:
                                builder = AlertDialogBuilder(fragment.getParentActivity())
                                builder.set_title(_tr("share_raw_title"))
                                builder.set_message(str(url))
                                builder.set_positive_button(_tr("share_copy_link"), lambda d, w: AndroidUtilities.addToClipboard(str(url)))
                                builder.set_neutral_button(_tr("share_open"), lambda d, w: open_link(str(url)))
                                builder.set_negative_button(_tr("cancel"), lambda d, w: d.dismiss())
                                builder.show()
                            except Exception as e:
                                log(f"[KPM] raw url dialog error: {e}")
                                open_link(str(url))

                        run_on_ui_thread(show_dialog)
                    except Exception as e:
                        log(f"[KPM] view_raw_url error: {e}")

                def send_to_tg():
                    def do_send():
                        try:
                            plugin_info = self.outer.pl.plugins_list.get(plugin_id)
                            if not plugin_info:
                                run_on_ui_thread(lambda: BulletinHelper.show_error(_tr("list_empty")))
                                return
                            url = plugin_info.get("url") if isinstance(plugin_info, dict) else plugin_info
                            if not url:
                                run_on_ui_thread(lambda: BulletinHelper.show_error(_tr("error_download").format("No URL")))
                                return

                            temp_path = os.path.join(PLUGINS_DIR, f"{plugin_id}.plugin")
                            data = self.outer.pl.fetch_remote_bytes(url)
                            with open(temp_path, "wb") as f:
                                f.write(data)

                            try:
                                from org.telegram.messenger import UserConfig
                                account = _get_current_account(fragment)
                                my_id = UserConfig.getInstance(account).getClientUserId()
                                run_on_ui_thread(lambda: send_document(my_id, temp_path, caption=f"{plugin_id}.plugin"))
                                BulletinHelper.show_success(_tr("share_send_file"))
                            except Exception as e:
                                run_on_ui_thread(lambda: BulletinHelper.show_error(str(e)))

                            def cleanup():
                                try:
                                    time.sleep(30)
                                    if os.path.exists(temp_path):
                                        os.remove(temp_path)
                                except Exception:
                                    pass
                            run_on_queue(cleanup)
                        except Exception as e:
                            err = str(e)
                            run_on_ui_thread(lambda err=err: BulletinHelper.show_error(_tr("error_download").format(err)))
                    run_on_queue(do_send)

                def send_as_file():
                    def do_send():
                        try:
                            plugin_info = self.outer.pl.plugins_list.get(plugin_id)
                            if not plugin_info:
                                run_on_ui_thread(lambda: BulletinHelper.show_error(_tr("list_empty")))
                                return
                            url = plugin_info.get("url") if isinstance(plugin_info, dict) else plugin_info
                            if not url:
                                run_on_ui_thread(lambda: BulletinHelper.show_error(_tr("error_download").format("No URL")))
                                return

                            temp_path = os.path.join(PLUGINS_DIR, f"{plugin_id}.plugin")
                            data = self.outer.pl.fetch_remote_bytes(url)
                            with open(temp_path, "wb") as f:
                                f.write(data)

                            def share_intent():
                                try:
                                    activity = fragment.getParentActivity()
                                    if not activity:
                                        return

                                    from org.telegram.messenger import ApplicationLoader
                                    from androidx.core.content import FileProvider
                                    from java.io import File
                                    from android.os import Build

                                    file_obj = File(temp_path)
                                    if Build.VERSION.SDK_INT >= 24:
                                        uri = FileProvider.getUriForFile(activity, ApplicationLoader.getApplicationId() + ".provider", file_obj)
                                    else:
                                        uri = Uri.fromFile(file_obj)

                                    intent = Intent(Intent.ACTION_SEND)
                                    intent.setType("application/octet-stream")
                                    intent.putExtra(Intent.EXTRA_STREAM, uri)
                                    intent.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION)
                                    intent.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
                                    activity.startActivity(Intent.createChooser(intent, _tr("share_title")))
                                    BulletinHelper.show_success(_tr("share_system"))
                                except Exception as e:
                                    BulletinHelper.show_error(str(e))

                            run_on_ui_thread(share_intent)

                            def cleanup():
                                try:
                                    if os.path.exists(temp_path):
                                        os.remove(temp_path)
                                except Exception:
                                    pass
                            run_on_queue(cleanup)
                        except Exception as e:
                            err = str(e)
                            run_on_ui_thread(lambda err=err: BulletinHelper.show_error(_tr("error_download").format(err)))

                    run_on_queue(do_send)

                def show_actions():
                    try:
                        try:
                            self.outer.pl._mkstats_event("share_menu_opened", 1)
                        except Exception:
                            pass
                        builder = AlertDialogBuilder(fragment.getParentActivity())
                        builder.set_title(_tr("share_title"))
                        builder.set_items([
                            _tr("share_copy_link"),
                            _tr("share_send_file"),
                            _tr("share_system"),
                        ], lambda _, which: (
                            copy_link() if which == 0 else
                            send_to_tg() if which == 1 else
                            send_as_file() if which == 2 else None
                        ))
                        builder.set_negative_button(_tr("cancel"), lambda d, w: d.dismiss())
                        builder.show()
                    except Exception as e:
                        log(f"[KPM] share actions error: {e}")

                run_on_ui_thread(show_actions)

            def togglePlugin(self, view):
                pass
        
        class PluginCellHook(MethodHook):
            def __init__(self, outer: "KangelPluginsManagerPlugin.PluginListFragment"):
                self.create_button_method = None
                self.outer = outer
                
            def after_hooked_method(self, param):
                from android_utils import OnClickListener
                from java import jint
                from java.lang import Boolean, Integer
                try:
                    this = param.thisObject
                    p = param.args[0]
                    if not p or p.getEngine() != __id__:
                        return
                    
                    try:
                        this.setNeedDivider(False)
                    except Exception:
                        pass
                    
                    get_private_field(this, "pinButton").setVisibility(View.GONE)
                    get_private_field(this, "checkBox").setVisibility(View.GONE)
                    get_private_field(this, "deleteButton").setVisibility(View.GONE)
                    plugin_id = p.getId()
                    plugin_info = self.outer.pl.plugins_list.get(plugin_id)
                    author = ""
                    description = ""
                    min_version = ""
                    app_version = ""
                    dependencies = []
                    requirements = []
                    status = "plugin"
                    if isinstance(plugin_info, dict):
                        author = plugin_info.get("author", "")
                        description = plugin_info.get("description", "")
                        min_version = plugin_info.get("min_version", "") or _normalize_min_version(plugin_info.get("app_version", ""))
                        app_version = plugin_info.get("app_version", "") or ""
                        dependencies = _normalize_requirements_list(plugin_info.get("dependencies", []) or [])
                        requirements = _normalize_requirements_list(plugin_info.get("requirements", []) or [])
                        status = plugin_info.get("status", "plugin") or "plugin"
                    client_version = self.outer.pl._mkstats_get_client_version()
                    version_compatible = True
                    if min_version and client_version and client_version != "unknown":
                        try:
                            def parse_ver(v):
                                return [int(x) if x.isdigit() else 0 for x in str(v).split(".")]
                            cv = parse_ver(client_version)
                            mv = parse_ver(min_version)
                            for i in range(max(len(cv), len(mv))):
                                c = cv[i] if i < len(cv) else 0
                                m = mv[i] if i < len(mv) else 0
                                if c < m:
                                    version_compatible = False
                                    break
                                elif c > m:
                                    break
                        except Exception as e:
                            log(f"[KPM] Version parse error: {e}")
                            version_compatible = False
                    elif min_version:
                        log(f"[KPM] No client version available, marking as incompatible")
                        version_compatible = False
                    if not version_compatible and min_version:
                        description = _tr("requires_version").format(min_version)
                    
                    desc = get_private_field(this, "subtitleView")
                    reserve_right_dp = AndroidUtilities.dp(170) if requirements else 0
                    try:
                        title_view = get_private_field(this, "titleView")
                        title_view.setPadding(title_view.getPaddingLeft(), title_view.getPaddingTop(), reserve_right_dp, title_view.getPaddingBottom())
                    except Exception:
                        pass
                    try:
                        desc.setPadding(desc.getPaddingLeft(), desc.getPaddingTop(), reserve_right_dp, desc.getPaddingBottom())
                    except Exception:
                        pass
                    if self.outer.type == KangelPluginsManagerPlugin.UPDATE:
                        old, new = self.outer.display_names["vers"][plugin_id]
                        label = f'{old} -> {new}'
                        s = SpannableString(label)
                        try:
                            s.setSpan(StrikethroughSpan(), 0, len(old), Spanned.SPAN_EXCLUSIVE_EXCLUSIVE)
                        except Exception:
                            pass
                        desc.setText(s)
                    else:
                        version_text = p.getVersion() or ""
                        if author:
                            if version_text:
                                author_spannable, _ = _parse_markdown(author)
                                if author_spannable:
                                    from android.text import SpannableStringBuilder
                                    full_text = f"{version_text} • "
                                    builder = SpannableStringBuilder(full_text)
                                    builder.append(author_spannable)
                                    desc.setText(builder)
                                else:
                                    desc.setText(f"{version_text} • {author}")
                            else:
                                spannable, _ = _parse_markdown(author)
                                if spannable:
                                    desc.setText(spannable)
                                else:
                                    desc.setText(author)
                        else:
                            desc.setText(version_text)

                    try:
                        bubbles = this.findViewWithTag("kpm_bubbles")
                        if bubbles:
                            this.removeView(bubbles)
                    except Exception:
                        pass
                    try:
                        requirements_badge = this.findViewWithTag("kpm_requirements_badge")
                        if requirements_badge:
                            this.removeView(requirements_badge)
                    except Exception:
                        pass
                    bubbles = None
                    requirements_badge = None
                    try:
                        bubbles_enabled = self.outer.pl.get_setting("show_plugin_bubbles", True)
                        if not bubbles_enabled:
                            raise Exception("bubbles disabled")
                            
                        ctx2 = this.getContext()
                        bubbles = LinearLayout(ctx2)
                        bubbles.setTag("kpm_bubbles")
                        bubbles.setOrientation(LinearLayout.HORIZONTAL)
                        bubbles.setGravity(Gravity.LEFT)
                        try:
                            bubbles.setPadding(AndroidUtilities.dp(12), AndroidUtilities.dp(4), AndroidUtilities.dp(12), AndroidUtilities.dp(4))
                        except Exception:
                            pass

                        def _make_bubble(text, color_key, alpha=0x22):
                            tv = TextView(ctx2)
                            tv.setText(str(text))
                            try:
                                tv.setTextSize(TypedValue.COMPLEX_UNIT_DIP, 12)
                            except Exception:
                                pass
                            tv.setSingleLine(True)
                            try:
                                tv.setEllipsize(TextUtils.TruncateAt.END)
                            except Exception:
                                pass
                            try:
                                tv.setTypeface(AndroidUtilities.bold())
                            except Exception:
                                pass
                            try:
                                c = Theme.getColor(color_key)
                            except Exception:
                                c = Theme.getColor(Theme.key_windowBackgroundWhiteBlueHeader)
                            try:
                                tv.setTextColor(c)
                            except Exception:
                                pass
                            try:
                                bg = Theme.createRoundRectDrawable(AndroidUtilities.dp(14), (c & 0x00FFFFFF) | (alpha << 24))
                                tv.setBackground(bg)
                            except Exception:
                                pass
                            try:
                                tv.setPadding(AndroidUtilities.dp(10), AndroidUtilities.dp(4), AndroidUtilities.dp(10), AndroidUtilities.dp(4))
                            except Exception:
                                pass
                            try:
                                tv.setMaxWidth(AndroidUtilities.dp(150))
                            except Exception:
                                pass
                            lp = LinearLayout.LayoutParams(-2, -2)
                            lp.rightMargin = AndroidUtilities.dp(6)
                            tv.setLayoutParams(lp)
                            return tv

                        try:
                            bubbles.addView(_make_bubble(_status_label(status), Theme.key_windowBackgroundWhiteBlueHeader, alpha=0x18))
                        except Exception:
                            pass

                        try:
                            is_lib = False
                            try:
                                if plugin_id in (self.outer.pl._all_deps_set if hasattr(self.outer.pl, "_all_deps_set") else set()):
                                    is_lib = True
                            except Exception:
                                is_lib = False
                            if (not is_lib) and "lib" in str(plugin_id).lower():
                                is_lib = True
                            if is_lib and status != "library":
                                bubbles.addView(_make_bubble(_tr("status_library"), Theme.key_windowBackgroundWhiteBlueText, alpha=0x18))
                        except Exception:
                            pass

                        try:
                            dep_names = []
                            for dep_id in dependencies:
                                try:
                                    dep_info = self.outer.pl.plugins_list.get(dep_id)
                                    if isinstance(dep_info, dict) and dep_info.get("name"):
                                        dep_names.append(dep_info.get("name"))
                                    else:
                                        dep_names.append(str(dep_id))
                                except Exception:
                                    dep_names.append(str(dep_id))
                            dep_text = ", ".join(dep_names[:2])
                            if len(dep_names) > 2:
                                dep_text += f" +{len(dep_names) - 2}"
                            if dep_text:
                                bubbles.addView(_make_bubble(dep_text, Theme.key_windowBackgroundWhiteBlueText, alpha=0x18))
                        except Exception:
                            pass

                        added = False
                        try:
                            this.addView(bubbles, LayoutHelper.createFrame(-2, -2, Gravity.LEFT | Gravity.BOTTOM, 12, 0, 104, 8))
                            added = True
                        except Exception:
                            added = False

                        if not added:
                            try:
                                this.addView(bubbles)
                            except Exception:
                                pass
                    except Exception:
                        pass

                    
                    description_view = get_private_field(this, "descriptionView")
                    try:
                        description_view.setPadding(description_view.getPaddingLeft(), description_view.getPaddingTop(), reserve_right_dp, description_view.getPaddingBottom())
                    except Exception:
                        pass
                    if description:
                        description_view.setVisibility(View.VISIBLE)
                        if not version_compatible and min_version:
                            try:
                                description_view.setTextColor(-0x10000)
                                description_view.setTypeface(AndroidUtilities.bold())
                                description_view.invalidate()
                            except Exception:
                                pass
                        spannable, plain = _parse_markdown(description)
                        if spannable:
                            description_view.setText(spannable)
                            try:
                                from android.text.method import LinkMovementMethod
                                description_view.setMovementMethod(LinkMovementMethod.getInstance())
                            except Exception:
                                pass
                        else:
                            description_view.setText(plain)
                        description_view.invalidate()
                        description_view.setMaxLines(10 ** 8)
                        description_view.setEllipsize(TextUtils.TruncateAt.END)
                    else:
                        description_view.setVisibility(View.GONE)
                    share_button = get_private_field(this, "shareButton")
                    if self.outer.type != KangelPluginsManagerPlugin.INSTALL:
                        share_button.setVisibility(View.GONE)
                    parent = share_button.getParent()
                    if parent:
                        parent.setVisibility(View.VISIBLE)

                    try:
                        bg_color = Theme.getColor(Theme.key_dialogSearchBackground)
                        spacing = AndroidUtilities.dp(4)
                        card_bg = Theme.createRoundRectDrawable(AndroidUtilities.dp(12), bg_color)
                        this.setBackground(InsetDrawable(card_bg, 0, spacing, 0, spacing))
                    except Exception:
                        pass

                    try:
                        lp = this.getLayoutParams()
                        if lp and hasattr(lp, "setMargins"):
                            m = AndroidUtilities.dp(8)
                            lp.setMargins(0, m // 2, 0, m // 2)
                            this.setLayoutParams(lp)
                    except Exception:
                        pass

                    try:
                        this.requestLayout()
                        this.invalidate()
                    except Exception:
                        pass
                    
                    
                    if not self.create_button_method:
                        self.create_button_method = this.getClass().getDeclaredMethod("createButton", Context, Integer.TYPE, Boolean.TYPE, View.OnClickListener)
                        self.create_button_method.setAccessible(True)
                       
                    def create_button(icon, fn):
                        return self.create_button_method.invoke(
                            this,
                            get_last_fragment().getContext(), 
                            jint(icon), 
                            False, 
                            OnClickListener(lambda *_: fn()))
                        
                    button = None
                    view_button = None
                    if self.outer.type == KangelPluginsManagerPlugin.INSTALL:
                        button = create_button(R_tg.drawable.msg_download, lambda: self.outer.pl.show_plugin_info_and_install(p.getId()))
                        def open_raw():
                            try:
                                try:
                                    self.outer.pl._mkstats_event("raw_opened", 1)
                                except Exception:
                                    pass
                                plugin_id2 = p.getId()
                                plugin_info2 = self.outer.pl.plugins_list.get(plugin_id2)
                                if not plugin_info2:
                                    run_on_ui_thread(lambda: BulletinHelper.show_error(_tr("list_empty")))
                                    return
                                url2 = plugin_info2.get("url") if isinstance(plugin_info2, dict) else plugin_info2
                                if not url2:
                                    run_on_ui_thread(lambda: BulletinHelper.show_error(_tr("error_download").format("No URL")))
                                    return
                                open_link(str(url2))
                            except Exception as e:
                                log(f"[KPM] open_raw error: {e}")
                        try:
                            view_button = create_button(R_tg.drawable.menu_instant_view, open_raw)
                        except Exception:
                            view_button = create_button(R_tg.drawable.menu_instant_view, open_raw)
                    elif self.outer.type == KangelPluginsManagerPlugin.UPDATE:
                        def on_update():
                            self.outer.plugin_ids.remove(p.getId())
                            self.outer.adapter.update(True)
                        button = create_button(R_tg.drawable.menu_browser_refresh, lambda: self.outer.pl.update_selected_plugins([p.getId()], on_update)) 
                    existing_layout = this.findViewWithTag("kpm_buttons")
                    if existing_layout:
                        this.removeView(existing_layout)
                    
                    new_buttons_layout = LinearLayout(get_last_fragment().getContext())
                    new_buttons_layout.setTag("kpm_buttons")
                    new_buttons_layout.setOrientation(LinearLayout.HORIZONTAL)
                    gravity = Gravity.BOTTOM
                    if self.outer.type == KangelPluginsManagerPlugin.INSTALL:
                        gravity = Gravity.BOTTOM
                        if share_button.getParent():
                            share_button.getParent().removeView(share_button)
                        new_buttons_layout.addView(share_button, share_button.getLayoutParams())
                        if view_button is not None:
                            new_buttons_layout.addView(view_button, share_button.getLayoutParams())
                    
                    if button is not None:
                         new_buttons_layout.addView(button, share_button.getLayoutParams())
                     
                    this.addView(new_buttons_layout, LayoutHelper.createFrame(-2, -2, gravity | Gravity.RIGHT, 0, 0, 0, 8))
                    try:
                        delay = 0
                        try:
                            parent = this.getParent()
                            if parent and hasattr(parent, 'indexOfChild'):
                                idx = parent.indexOfChild(this)
                                delay = min(idx * 50, 300)
                        except:
                            pass
                        this.setAlpha(0.0)
                        this.setScaleX(0.85)
                        this.setScaleY(0.85)
                        this.setTranslationY(AndroidUtilities.dp(40))
                        
                        def start_animation():
                            try:
                                this.animate() \
                                    .alpha(1.0) \
                                    .scaleX(1.0) \
                                    .scaleY(1.0) \
                                    .translationY(0.0) \
                                    .setDuration(250) \
                                    .setInterpolator(OvershootInterpolator(1.2)) \
                                    .start()
                            except:
                                pass
                        
                        if delay > 0:
                            run_on_ui_thread(start_animation, delay)
                        else:
                            start_animation()
                    except Exception:
                        pass
                    
                except Exception as e:
                    log(str(e))
        
        
        def __init__(self, pl: "KangelPluginsManagerPlugin", title, plugin_ids, display_names, type = 0):
            super().__init__()
            self.title = title
            self.plugin_ids = plugin_ids
            self.display_names = display_names
            self.pl = pl
            self.search_query = None
            self.adapter = None
            self.type = type
            self.fill_id = 0
            self.scroll_controls = None
            self.scroll_label = None
            self.scroll_icon = None
            self.scroll_listener = None
            self.scroll_controls_visible = True

        def _scroll_list_to(self, edge):
            try:
                if not getattr(self, "recycler", None):
                    return
                adapter = self.recycler.getAdapter() if hasattr(self.recycler, "getAdapter") else None
                item_count = adapter.getItemCount() if adapter and hasattr(adapter, "getItemCount") else 0
                if item_count <= 0:
                    return
                position = 0 if edge == "top" else max(0, item_count - 1)
                try:
                    self.recycler.smoothScrollToPosition(position)
                except Exception:
                    self.recycler.scrollToPosition(position)
            except Exception as e:
                log(f"[KPM] _scroll_list_to({edge}) failed: {e}")

        def _handle_scroll_control_click(self):
            try:
                self._scroll_list_to("bottom")
            except Exception as e:
                log(f"[KPM] _handle_scroll_control_click failed: {e}")

        def _update_scroll_control_state(self):
            try:
                if not self.scroll_controls or not self.scroll_label or not self.scroll_icon or not getattr(self, "recycler", None):
                    return
                adapter = self.recycler.getAdapter() if hasattr(self.recycler, "getAdapter") else None
                item_count = adapter.getItemCount() if adapter and hasattr(adapter, "getItemCount") else 0
                if item_count <= 1:
                    self.scroll_controls.setVisibility(View.GONE)
                    self.scroll_controls_visible = False
                    return
                self.scroll_label.setText("В конец списка")
                self.scroll_icon.setImageResource(R_tg.drawable.msg_go_down)
                if self.scroll_controls_visible:
                    self.scroll_controls.setVisibility(View.VISIBLE)
            except Exception as e:
                log(f"[KPM] _update_scroll_control_state failed: {e}")

        def _set_scroll_control_visible(self, visible, animated=True):
            try:
                if not self.scroll_controls:
                    return
                if self.scroll_controls_visible == visible and self.scroll_controls.getVisibility() in [View.VISIBLE, View.GONE]:
                    return
                self.scroll_controls_visible = visible
                use_animation = bool(animated)
                if visible:
                    self.scroll_controls.setVisibility(View.VISIBLE)
                    if use_animation:
                        try:
                            self.scroll_controls.animate().cancel()
                        except Exception:
                            pass
                        self.scroll_controls.setAlpha(0.0)
                        self.scroll_controls.setTranslationY(AndroidUtilities.dp(18))
                        self.scroll_controls.setScaleX(0.92)
                        self.scroll_controls.setScaleY(0.92)
                        self.scroll_controls.animate() \
                            .alpha(1.0) \
                            .translationY(0.0) \
                            .scaleX(1.0) \
                            .scaleY(1.0) \
                            .setDuration(220) \
                            .setInterpolator(OvershootInterpolator(0.8)) \
                            .start()
                    else:
                        self.scroll_controls.setAlpha(1.0)
                        self.scroll_controls.setTranslationY(0.0)
                        self.scroll_controls.setScaleX(1.0)
                        self.scroll_controls.setScaleY(1.0)
                else:
                    if use_animation:
                        try:
                            self.scroll_controls.animate().cancel()
                        except Exception:
                            pass
                        self.scroll_controls.animate() \
                            .alpha(0.0) \
                            .translationY(AndroidUtilities.dp(28)) \
                            .scaleX(0.90) \
                            .scaleY(0.90) \
                            .setDuration(240) \
                            .start()
                        run_on_ui_thread(
                            lambda: self.scroll_controls.setVisibility(View.GONE) if (self.scroll_controls and not self.scroll_controls_visible) else None,
                            250
                        )
                    else:
                        self.scroll_controls.setAlpha(0.0)
                        self.scroll_controls.setTranslationY(AndroidUtilities.dp(28))
                        self.scroll_controls.setScaleX(0.90)
                        self.scroll_controls.setScaleY(0.90)
                        self.scroll_controls.setVisibility(View.GONE)
            except Exception as e:
                log(f"[KPM] _set_scroll_control_visible failed: {e}")
        
        def beforeCreateView(self):        
            self.content_view = FrameLayout(get_last_fragment().getContext())
            sys_md3 = False
            try:
                from jnius import autoclass
                ThemeEnforcement = autoclass("com.google.android.material.internal.ThemeEnforcement")
                if ThemeEnforcement:
                    ctx = get_last_fragment().getContext()
                    sys_md3 = bool(ThemeEnforcement.isMaterial3Theme(ctx))
            except Exception:
                sys_md3 = False
            
            self.md3_enabled = sys_md3
            self.content_view.setBackgroundColor(
                Theme.getColor(Theme.key_windowBackgroundGray)
            )

            self.recycler = UniversalRecyclerView(
                get_last_fragment(),
                self.Callback2(self.fillItems),
                self.Callback5(self.onClick),
                self.Callback5Return(self.onLongClick)
            )

            if not getattr(self, "md3_enabled", False):
                try:
                    self.recycler.setClipToPadding(False)
                except Exception:
                    pass
                try:
                    self.recycler.setPadding(
                        AndroidUtilities.dp(16),
                        AndroidUtilities.dp(8),
                        AndroidUtilities.dp(16),
                        AndroidUtilities.dp(8)
                    )
                except Exception:
                    pass
            else:

                try:
                    self.recycler.setClipToPadding(False)
                    self.recycler.setPadding(
                        0,
                        AndroidUtilities.dp(8),
                        0,
                        AndroidUtilities.dp(8)
                    )
                except Exception:
                    pass

            try:
                if hasattr(self.recycler, "adapter") and self.recycler.adapter and hasattr(self.recycler.adapter, "setApplyBackground"):
                    self.recycler.adapter.setApplyBackground(False)
            except Exception as e:
                log(f"[KPM] setApplyBackground(False) failed: {e}")

            self.content_view.addView(self.recycler, LayoutHelper.createFrame(-1, -1))

            try:
                from android_utils import OnClickListener
                controls = LinearLayout(get_last_fragment().getContext())
                controls.setOrientation(LinearLayout.HORIZONTAL)
                controls.setGravity(Gravity.CENTER_VERTICAL)
                controls.setPadding(AndroidUtilities.dp(14), AndroidUtilities.dp(10), AndroidUtilities.dp(12), AndroidUtilities.dp(10))
                controls.setOnClickListener(OnClickListener(lambda *_: self._handle_scroll_control_click()))
                try:
                    controls.setBackground(Theme.createRoundRectDrawable(
                        AndroidUtilities.dp(20),
                        Theme.getColor(Theme.key_featuredStickers_addButton)
                    ))
                except Exception:
                    pass

                label = TextView(get_last_fragment().getContext())
                label.setTextSize(TypedValue.COMPLEX_UNIT_DIP, 13)
                label.setTypeface(AndroidUtilities.bold())
                try:
                    label.setTextColor(Theme.getColor(Theme.key_featuredStickers_buttonText))
                except Exception:
                    pass
                label.setText("В конец списка")
                controls.addView(label, LinearLayout.LayoutParams(-2, -2))

                icon = ImageView(get_last_fragment().getContext())
                icon.setScaleType(ImageView.ScaleType.CENTER)
                icon.setImageResource(R_tg.drawable.msg_go_down)
                try:
                    icon.setColorFilter(Theme.getColor(Theme.key_featuredStickers_buttonText))
                except Exception:
                    pass
                icon_lp = LinearLayout.LayoutParams(AndroidUtilities.dp(20), AndroidUtilities.dp(20))
                icon_lp.leftMargin = AndroidUtilities.dp(8)
                controls.addView(icon, icon_lp)

                self.scroll_controls = controls
                self.scroll_label = label
                self.scroll_icon = icon
                self.scroll_controls.setAlpha(1.0)
                self.scroll_controls.setTranslationY(0.0)
                bottom_offset = 84 if self.type == KangelPluginsManagerPlugin.UPDATE and len(self.plugin_ids) > 0 else 28
                self.content_view.addView(controls, LayoutHelper.createFrame(-2, -2, Gravity.CENTER_HORIZONTAL | Gravity.BOTTOM, 0, 0, 0, bottom_offset))

                OnScrollChangeListener = find_class("android.view.View$OnScrollChangeListener")
                plugin_fragment = self
                class KPMScrollListener(dynamic_proxy(OnScrollChangeListener)):
                    def __init__(self):
                        super().__init__()
                    def onScrollChange(self, view, scrollX, scrollY, oldScrollX, oldScrollY):
                        dx = int(scrollX) - int(oldScrollX)
                        dy = int(scrollY) - int(oldScrollY)
                        if dy > 0:
                            plugin_fragment._set_scroll_control_visible(False, True)
                        elif dy < 0:
                            plugin_fragment._set_scroll_control_visible(True, True)
                        else:
                            pass

                self.scroll_listener = KPMScrollListener()
                try:
                    self.recycler.setOnScrollChangeListener(self.scroll_listener)
                except Exception:
                    pass
                run_on_ui_thread(lambda: self._update_scroll_control_state(), 50)
                run_on_ui_thread(lambda: self._set_scroll_control_visible(True, False), 50)
            except Exception as e:
                pass

            if self.type == KangelPluginsManagerPlugin.UPDATE and len(self.plugin_ids) > 0:
                from android_utils import OnClickListener
                updating = False
                def on_click(*_):
                    nonlocal updating
                    if updating:
                        return
                    updating = True
                    def on_update():
                        self.plugin_ids.clear()
                        self.adapter.update(True)
                    self.pl.update_selected_plugins(self.plugin_ids, on_update)
                    
                update_all_button = TextView(get_last_fragment().getContext())
                update_all_button.setPadding(AndroidUtilities.dp(34), 0, AndroidUtilities.dp(34), 0)
                update_all_button.setGravity(Gravity.CENTER)
                update_all_button.setTextSize(TypedValue.COMPLEX_UNIT_DIP, 14)
                update_all_button.setTypeface(AndroidUtilities.bold())
                update_all_button.setText(_tr("update_plugins"))

                update_all_button.setTextColor(Theme.getColor(Theme.key_featuredStickers_buttonText))
                update_all_button.setBackground(Theme.AdaptiveRipple.filledRectByKey(Theme.key_featuredStickers_addButton, 4))
                update_all_button.setOnClickListener(OnClickListener(on_click))
                self.content_view.addView(update_all_button, LayoutHelper.createFrame(-1, 48, Gravity.BOTTOM, 7, 0, 7, 0))

            return self.content_view
        
        def getTitle(self):
            return self.title
        
        def onBackPressed(self):
            get_last_fragment().finishFragment()
            return None
        
        def fillItems(self, items, adapter):
            self.adapter = adapter
            self.items = items
            self.fill_id += 1
            try:
                status_filter = str(self.pl.get_setting("plugins_status_filter", "*") or "*")
            except Exception:
                status_filter = "*"

            def _passes_status(pid):
                if status_filter == "*":
                    return True
                try:
                    info = self.pl.plugins_list.get(pid)
                    if isinstance(info, dict):
                        return (info.get("status") or "plugin") == status_filter
                except Exception:
                    pass
                return status_filter == "plugin"
            if self.search_query:
                query = str(self.search_query)
                if len(query.strip()) >= 3 and getattr(self.pl, "_trigram_index", None):
                    ranked = self.pl._trigram_search(query, allowed_ids=self.plugin_ids)
                    if ranked:
                        plugin_ids = [pid for pid in ranked if _passes_status(pid)]
                    else:
                        plugin_ids = []
                else:
                    def match(pid):
                        name = self.display_names.get(pid)
                        if not name:
                            name = pid
                        elif not isinstance(name, str):
                            name = name.get("name", pid)

                        query_lower = query.lower()
                        return query_lower in name.lower() or query_lower in pid.lower()

                    plugin_ids = [pid for pid in self.plugin_ids if match(pid) and _passes_status(pid)]
            else:
                plugin_ids = [pid for pid in self.plugin_ids if _passes_status(pid)]

            try:
                mode = int(self.pl.get_setting("plugins_sort_mode", 0) or 0)

                def _name_for_sort(pid):
                    name = self.display_names.get(pid)
                    if not name:
                        return pid
                    if isinstance(name, str):
                        return name
                    if isinstance(name, dict):
                        return name.get("name", pid)
                    return pid

                def _author_for_sort(pid):
                    try:
                        info = self.pl.plugins_list.get(pid)
                        if isinstance(info, dict):
                            return (info.get("author") or "").lower()
                    except Exception:
                        pass
                    return ""

                def _status_for_sort(pid):
                    try:
                        info = self.pl.plugins_list.get(pid)
                        if isinstance(info, dict):
                            return info.get("status", "plugin")
                    except Exception:
                        pass
                    return "plugin"

                if mode == 1:
                    plugin_ids = sorted(plugin_ids, key=lambda pid: _name_for_sort(pid).lower(), reverse=False)
                elif mode == 2:
                    plugin_ids = sorted(plugin_ids, key=lambda pid: _name_for_sort(pid).lower(), reverse=True)
                elif mode == 3:
                    plugin_ids = sorted(plugin_ids, key=lambda pid: (_author_for_sort(pid), _name_for_sort(pid).lower()), reverse=False)
                elif mode == 4:
                    plugin_ids = sorted(plugin_ids, key=lambda pid: (_author_for_sort(pid), _name_for_sort(pid).lower()), reverse=True)
                elif mode == 5:
                    plugin_ids = sorted(plugin_ids, key=lambda pid: (_status_sort_key(_status_for_sort(pid)), _name_for_sort(pid).lower()), reverse=False)

            except Exception as e:
                log(f"[KPM] Sort error: {e}")
            self.addItems(0, plugin_ids, items, self.fill_id)
            run_on_ui_thread(lambda: self._update_scroll_control_state(), 50)
        
        chunk_size = 25
        def addItems(self, i, plugins_ids, items, fid):
            try:
                if fid != self.fill_id:
                    return
                from_ = i*self.chunk_size
                len_ = len(plugins_ids)
                get_ = min(self.chunk_size, len_ - from_)
                stop = from_ + get_
                for j in range(from_, stop):
                    pid = plugins_ids[j]
                    if self.type == KangelPluginsManagerPlugin.UPDATE:
                        name = self.display_names["d"].get(pid, pid)
                    else:
                        name = self.display_names.get(pid, pid)
                        
                    p = Plugin(pid, name)
                    p.setEngine(__id__)
                    icon = None
                    ver = None
                    if self.type == KangelPluginsManagerPlugin.INSTALL:
                        info = self.pl.plugins_list.get(pid)
                        if not info:
                            continue
                        icon = info.get("icon")
                        ver = info.get("version")  
                    elif self.type == KangelPluginsManagerPlugin.UPDATE:
                        info = self.pl.plugins_list.get(pid)
                        if info:
                            icon = info.get("icon")
                            ver = info.get("version")
                        
                    if isinstance(icon, str):
                        p.setIcon(icon) 
                    if isinstance(ver, str):
                        p.setVersion(ver)   
                        
                    from com.exteragram.messenger.plugins.ui.components import \
                        PluginCell
                    try:
                        if hasattr(PluginCell, "Factory") and getattr(PluginCell, "Factory") is not None:
                            items.add(PluginCell.Factory.asPlugin(p, self.PluginCellDelegate(pid, self)))
                        else:
                            if not getattr(self.pl, "_kpm_logged_no_plugin_cell_factory", False):
                                self.pl._kpm_logged_no_plugin_cell_factory = True
                                log("[KPM] PluginCell.Factory is missing, using UItem.asPlugin")
                            items.add(UItem.asPlugin(1, p, self.PluginCellDelegate(pid, self)))
                    except Exception as e:
                        try:
                            items.add(UItem.asPlugin(1, p, self.PluginCellDelegate(pid, self)))
                        except Exception as e2:
                            log(f"[KPM] UItem.asPlugin failed: {e2}")
                if stop >= len_ and self.type == KangelPluginsManagerPlugin.UPDATE:
                    items.add(UItem.asSpace(AndroidUtilities.dp(48)))
                
                if i != 0:
                    self.adapter.notifyItemRangeInserted(from_, get_)
                
                if stop >= len_:
                    run_on_ui_thread(lambda: self._update_scroll_control_state(), 50)
                    return
                delay = 100 if i < 2 else 200
                run_on_ui_thread(lambda: self.addItems(i + 1, plugins_ids, items, fid), delay)
            except Exception as e:
                log(str(e))
        
        def onClick(self, item, view, position, x, y):
            return False
    
        def onLongClick(self, item, view, position, x, y):
            return False
        
        def afterCreateView(self, view):
            pass
        
        def onFragmentCreate(self, *_):
            from com.exteragram.messenger.plugins.ui.components import \
                PluginCell
            self.set_hook = self.pl.hook_method(PluginCell.getClass().getDeclaredMethod("set", Plugin, PluginCellDelegate), self.PluginCellHook(self))

            if getattr(self, "md3_enabled", False):
                try:
                    adapter2 = self.recycler.getAdapter()
                    if adapter2 and hasattr(adapter2, "setApplyBackground"):
                        adapter2.setApplyBackground(True)
                        try:
                            self.recycler.invalidateItemDecorations()
                        except Exception:
                            pass
                        try:
                            adapter2.notifyDataSetChanged()
                        except Exception:
                            pass
                        try:
                            self.recycler.requestLayout()
                            self.recycler.invalidate()
                        except Exception:
                            pass
                    else:
                        self.md3_enabled = False
                except Exception:
                    self.md3_enabled = False

            if not getattr(self, "md3_enabled", False):
                try:
                    self.content_view.setBackgroundColor(Theme.getColor(Theme.key_windowBackgroundWhite))
                except Exception:
                    pass
        
        def onFragmentDestroy(self, *_):
            self.fill_id += 1
            try:
                if self.content_view:
                    parent = self.content_view.getParent()
                    if parent and hasattr(parent, 'removeView'):
                        parent.removeView(self.content_view)
            except Exception:
                pass
            if self.set_hook:
                self.pl.unhook_method(self.set_hook)
            if self.pl.search_listener_hooks:
                for h in self.pl.search_listener_hooks:
                    self.pl.unhook_method(h)
            self.set_hook = None
            self.pl.search_listener_hooks = None
            self.scroll_controls = None
            self.scroll_label = None
            self.scroll_icon = None
            self.scroll_listener = None
            
        def onMenuItemClick(self, *_):
            pass

    def list_installed_plugins(self):
        installed = []
        try:
            if not os.path.isdir(PLUGINS_DIR):
                return installed
            if hasattr(self, '_installed_cache_time') and (time.time() - self._installed_cache_time) < 5:
                if hasattr(self, '_installed_cache'):
                    return self._installed_cache

            files = os.listdir(PLUGINS_DIR)
            for name in files:
                if not name.endswith(".py"):
                    continue
                path = os.path.join(PLUGINS_DIR, name)
                try:
                    with open(path, "rb") as f:
                        content = f.read()
                    
                    plugin_id = None
                    if content:
                        import re
                        match = re.search(rb'__id__\s*=\s*["\'](.*?)["\']', content)
                        if match:
                            plugin_id = match.group(1).decode('utf-8', errors='ignore')
                    
                    if not plugin_id:
                        plugin_id = name[:-3]
                    
                    installed.append(plugin_id)
                except Exception:
                    continue

            installed = list(set(installed))
            self._installed_cache = installed
            self._installed_cache_time = time.time()
            
            return installed
        except Exception as e:
            log(f"[KPM] Error listing installed plugins: {e}")
            return installed

    def get_local_plugin_path(self, plugin_id):
        return os.path.join(PLUGINS_DIR, f"{plugin_id}.plugin")

    def read_file_bytes(self, path):
        try:
            with open(path, "rb") as f:
                return f.read()
        except Exception:
            return None

    def sha256(self, data):
        h = hashlib.sha256()
        h.update(data)
        return h.hexdigest()

    def fetch_remote_bytes(self, url):
        r = requests.get(url, timeout=30)
        if r.status_code != 200:
            raise Exception(f"HTTP {r.status_code}")
        return r.content

    def install_plugin_by_id(self, plugin_id, _installing_deps=None, enable_after=False):
        def do_install():
            try:
                deps_set = _installing_deps if _installing_deps is not None else set()
                if plugin_id in deps_set:
                    return              
                if not self.plugins_list:
                    self.refresh_store()             
                if plugin_id not in self.plugins_list:
                    error_msg = f"Plugin {plugin_id} not found in store"
                    run_on_ui_thread(lambda: BulletinHelper.show_error(error_msg))
                    return
                
                plugin_info = self.plugins_list[plugin_id]
                if not self._ensure_plugin_version_supported(plugin_id, plugin_info):
                    return
                url = plugin_info.get("url") if isinstance(plugin_info, dict) else plugin_info
                dependencies = plugin_info.get("dependencies", []) if isinstance(plugin_info, dict) else []
                
                remote = self.fetch_remote_bytes(url)
                
                target = os.path.join(PLUGINS_DIR, f"{plugin_id}.py")
                tmp = target + ".tmp"
                
                with open(tmp, "wb") as f:
                    f.write(remote)
                
                if os.path.exists(target):
                    os.remove(target)
                shutil.move(tmp, target)
                
                def notify_installed():
                    try:
                        controller = PluginsController.getInstance()
                        if controller and hasattr(controller, 'engines'):
                            engine = controller.engines.get("python")
                            if engine:
                                engine.loadPlugins(None)
                        NotificationCenter.getGlobalInstance().postNotificationName(NotificationCenter.pluginsUpdated)
                        
                        if enable_after:
                            controller.setPluginEnabled(plugin_id, True, None)
                    except Exception as e:
                        log(f"[KPM] Error reloading plugins: {e}")
                    BulletinHelper.show_error(_tr("installed").format(f"{plugin_id}.py"))
                
                run_on_ui_thread(notify_installed)
            except Exception as e:
                log(f"[KPM] ERROR installing {plugin_id}: {e}")
                run_on_ui_thread(lambda: BulletinHelper.show_error(_tr("error_write").format(e)))

        run_on_queue(do_install)

    def update_installed_from_store(self):
        if not self.plugins_list:
            self.refresh_store()
        if not self.plugins_list:
            return
        updated = 0
        skipped = 0
        failed = 0
        installed_ids = self.list_installed_plugins()
        for pid in installed_ids:
            plugin_info = self.plugins_list.get(pid)
            if not plugin_info:
                continue
            url = plugin_info.get("url") if isinstance(plugin_info, dict) else plugin_info
            local_path = os.path.join(PLUGINS_DIR, f"{pid}.py")
            if not os.path.exists(local_path):
                continue
            
            try:
                local_bytes = self.read_file_bytes(local_path)
                if not local_bytes:
                    continue
                local_metadata = self.parse_plugin_metadata(local_bytes)
                local_version = local_metadata.get("version", "1.0")
                remote_version = str(plugin_info.get("version", "0"))
                if remote_version != local_version:
                    try:
                        remote = self.fetch_remote_bytes(url)
                        tmp = local_path + ".tmp"
                        with open(tmp, "wb") as f:
                            f.write(remote)
                        if os.path.exists(local_path):
                            os.remove(local_path)
                        shutil.move(tmp, local_path)
                        updated += 1
                    except Exception:
                        failed += 1
                else:
                    skipped += 1
            except Exception:
                failed += 1
        run_on_ui_thread(lambda: BulletinHelper.show_error(_tr("updated_stats").format(updated, skipped, failed)))


    def _show_import_collection_dialog(self):
        try:
            from android.app import Activity

            fragment = get_last_fragment()
            if not fragment:
                return

            intent = Intent(Intent.ACTION_OPEN_DOCUMENT)
            intent.addCategory(Intent.CATEGORY_OPENABLE)
            intent.setType("*/*")
            
            activity = fragment.getParentActivity()
            if not activity:
                return

            REQUEST_CODE_KPM_IMPORT = 4242

            def on_activity_result(requestCode, resultCode, data):
                if requestCode != REQUEST_CODE_KPM_IMPORT or resultCode != Activity.RESULT_OK or data is None:
                    return

                uri = data.getData()
                if uri is None:
                    return
                
                try:
                    input_stream = activity.getContentResolver().openInputStream(uri)
                    temp_path = os.path.join(self.plugins_dir, ".temp_collection.kpm")
                    
                    with open(temp_path, "wb") as f_out:
                        buffer = bytearray(4096)
                        bytes_read = input_stream.read(buffer)
                        while bytes_read != -1:
                            f_out.write(buffer[:bytes_read])
                            bytes_read = input_stream.read(buffer)
                    
                    if input_stream:
                        input_stream.close()

                    import_collection(self, temp_path)
                except Exception as e:
                    log(f"[KPM] Error reading collection file: {e}")
                finally:
                    if hasattr(self, "_import_hook_ref") and self._import_hook_ref:
                        self.unhook_method(self._import_hook_ref)
                        self._import_hook_ref = None

            class OnActivityResultHook(MethodHook):
                def __init__(self, plugin, callback):
                    self.plugin_ref = weakref.ref(plugin)
                    self.callback = callback
                def after_hooked_method(self, param):
                    plugin = self.plugin_ref()
                    if not plugin:
                        return
                    
                    req_code = param.args[0]
                    if req_code == REQUEST_CODE_KPM_IMPORT:
                        self.callback(req_code, param.args[1], param.args[2])

            from java.lang import Integer
            method = activity.getClass().getDeclaredMethod("onActivityResult", Integer.TYPE, Integer.TYPE, Intent)
            method.setAccessible(True)
            self._import_hook_ref = self.hook_method(method, OnActivityResultHook(self, on_activity_result))
            fragment.startActivityForResult(intent, REQUEST_CODE_KPM_IMPORT)
        except Exception as e:
            log(f"[KPM] Error opening file picker: {e}")

    class CollectionPickerFragment(dynamic_proxy(UniversalFragment.UniversalFragmentDelegate)):
        def __init__(self, pl, title, all_plugin_ids, initial_selected_ids, on_done):
            super().__init__()
            self.pl = pl
            self.title = title
            self.all_plugin_ids = all_plugin_ids
            self.selected_ids = set(initial_selected_ids)
            self.on_done = on_done
            self.adapter = None
            self.search_query = None

        def getTitle(self):
            return self.title

        def onBackPressed(self):
            get_last_fragment().finishFragment()
            return True

        def beforeCreateView(self):
            self.content_view = FrameLayout(get_last_fragment().getContext())
            self.content_view.setBackgroundColor(Theme.getColor(Theme.key_windowBackgroundGray))
            self.recycler = UniversalRecyclerView(
                get_last_fragment(),
                KangelPluginsManagerPlugin.PluginListFragment.Callback2(self.fillItems),
                KangelPluginsManagerPlugin.PluginListFragment.Callback5(self.onClick),
                None
            )
            self.content_view.addView(self.recycler, LayoutHelper.createFrame(-1, -1))
            return self.content_view

        def onFragmentCreate(self, *args):
            fragment = get_last_fragment()
            action_bar = fragment.getActionBar()

            from org.telegram.ui.ActionBar import ActionBarMenuItem
            from java.lang import CharSequence, Integer, Boolean
            from base_plugin import MethodHook

            item = action_bar.createMenu().addItem(0, R_tg.drawable.ic_ab_search).setIsSearchField(True)
            search_field = item.getSearchField()
            
            delegate = self

            class SearchHook(MethodHook):
                def before_hooked_method(self, param):
                    try:
                        new_query = search_field.getText().toString()
                        if delegate.search_query != new_query:
                            delegate.search_query = new_query
                            if delegate.adapter:
                                delegate.adapter.update(True)
                    except Exception as e:
                        log(f"[KPM] Search hook error: {e}")
                
                def after_hooked_method(self, param):
                    pass
            
            try:
                from java.util import ArrayList
                listeners_field = search_field.getClass().getDeclaredField("mListeners")
                listeners_field.setAccessible(True)
                listeners = listeners_field.get(search_field)
                if listeners and listeners.size() > 0:
                    text_listener = listeners.get(0)
                    self.search_hook = self.pl.hook_method(text_listener.getClass().getDeclaredMethod("onTextChanged", CharSequence, Integer.TYPE, Integer.TYPE, Integer.TYPE), SearchHook())
                    log("[KPM] Search hook installed via mListeners")
                else:
                    log("[KPM] No text listeners found")
            except Exception as e:
                log(f"[KPM] Could not install search hook: {e}")

            class CollapseHook(MethodHook):
                def after_hooked_method(self, param):
                    if param.thisObject != item or param.args[0]:
                        return
                    param.setResult(None)
                    if delegate.search_query is not None:
                        delegate.search_query = None
                        if delegate.adapter:
                            delegate.adapter.update(True)
            
            self.collapse_hook = self.pl.hook_method(ActionBarMenuItem.getClass().getDeclaredMethod("toggleSearch", Boolean.TYPE), CollapseHook())
            action_bar.createMenu().addItem(1, _tr("done")).setOnClickListener(self.DoneClickListener(self))

        def onFragmentDestroy(self, *args):
            if hasattr(self, "search_hook") and self.search_hook:
                self.pl.unhook_method(self.search_hook)
            if hasattr(self, "collapse_hook") and self.collapse_hook:
                self.pl.unhook_method(self.collapse_hook)

        def fillItems(self, items, adapter):
            self.adapter = adapter
            filtered_ids = self.all_plugin_ids
            if self.search_query:
                q = self.search_query.lower()
                filtered_ids = [pid for pid in self.all_plugin_ids if q in self.pl.get_plugin_display_name(pid).lower() or q in pid.lower()]

            for pid in sorted(filtered_ids, key=lambda id: self.pl.get_plugin_display_name(id).lower()):
                items.add(UItem.asCheck(pid, self.pl.get_plugin_display_name(pid), pid in self.selected_ids))

        def onClick(self, item, view, position, x, y):
            if item.id in self.selected_ids:
                self.selected_ids.remove(item.id)
            else:
                self.selected_ids.add(item.id)
            item.checked = not item.checked
            view.setChecked(item.checked)

        class DoneClickListener(dynamic_proxy(View.OnClickListener)):
            def __init__(self, delegate):
                super().__init__()
                self.delegate = delegate
            def onClick(self, v):
                self.delegate.on_done(sorted(list(self.delegate.selected_ids)))
                get_last_fragment().finishFragment()
