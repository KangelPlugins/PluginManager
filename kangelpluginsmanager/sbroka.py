
import json
import os

from org.telegram.messenger import UserConfig
from client_utils import send_document, get_last_fragment
from ui.alert import AlertDialogBuilder

from .methods import _normalize_requirements_list, _tr, log


def normalize_collection_plugins(raw_plugins):
    result = []
    seen = set()
    KPM_ID = "kangel_plugins_manager"
    for item in raw_plugins or []:
        plugin_id = ""
        if isinstance(item, dict):
            plugin_id = str(item.get("id") or item.get("plugin_id") or "").strip()
        else:
            text = str(item or "").strip()
            if text.startswith("tg://kpm_install?plugin="):
                plugin_id = text.split("=", 1)[-1].strip()
            else:
                plugin_id = text
        if plugin_id == KPM_ID:
            continue
        if plugin_id and plugin_id not in seen:
            seen.add(plugin_id)
            result.append(plugin_id)
    return result


def build_collection_payload(metadata, plugin_ids):
    clean_metadata = {
        "name": str((metadata or {}).get("name") or "").strip(),
        "author": str((metadata or {}).get("author") or "").strip(),
        "description": str((metadata or {}).get("description") or "").strip(),
        "icon": str((metadata or {}).get("icon") or "").strip(),
    }
    normalized_ids = normalize_collection_plugins(plugin_ids)
    return {
        "metadata": clean_metadata,
        "plugins": [f"tg://kpm_install?plugin={pid}" for pid in normalized_ids],
        "format": "kpm_collection_v2",
    }


def load_collection_file(file_path):
    # Resolve relative paths
    resolved_path = file_path
    if not os.path.isabs(file_path):
        # Try current directory first
        if os.path.exists(file_path):
            resolved_path = os.path.abspath(file_path)
        else:
            # Try common locations
            from client_utils import get_account_plugins_dir
            account_plugins_dir = get_account_plugins_dir() if callable(get_account_plugins_dir) else None
            if account_plugins_dir:
                test_path = os.path.join(account_plugins_dir, file_path)
                if os.path.exists(test_path):
                    resolved_path = test_path
    
    # Check file exists
    if not os.path.exists(resolved_path):
        log(f"[KPM] Collection file not found: {file_path} (resolved: {resolved_path})")
        raise FileNotFoundError(f"Collection file not found: {file_path}")
    
    try:
        with open(resolved_path, "r", encoding="utf-8") as f:
            collection = json.load(f)
    except json.JSONDecodeError as jde:
        log(f"[KPM] Invalid JSON in collection file {resolved_path}: {jde}")
        raise ValueError(f"Invalid collection file: {jde}") from jde
    
    metadata = dict(collection.get("metadata") or {})
    plugin_ids = normalize_collection_plugins(
        collection.get("plugins") or collection.get("links") or []
    )
    return metadata, plugin_ids, collection


def export_collection(plugin_instance, metadata, plugin_ids):
    try:
        from ui.bulletin import BulletinHelper
        
        collection = build_collection_payload(metadata, plugin_ids)
        collection_name = collection["metadata"].get("name") or "kpm_collection"
        safe_name = "".join(ch if ch.isalnum() or ch in "-_ " else "_" for ch in collection_name).strip() or "kpm_collection"
        file_path = os.path.join(plugin_instance.plugins_dir, f"{safe_name}.kpm")
        with open(file_path, "w", encoding="utf-8") as f:
            json.dump(collection, f, ensure_ascii=False, indent=4)

        current_account = UserConfig.selectedAccount
        user_id = UserConfig.getInstance(current_account).getClientUserId()
        send_document(user_id, file_path, caption=_tr("collection_exported"))
        BulletinHelper.show_success(_tr("collection_exported"))
    except Exception as e:
        from ui.bulletin import BulletinHelper
        log(f"[KPM] Export collection error: {e}")
        BulletinHelper.show_error(_tr("collection_error").format(e))


def import_collection(plugin_instance, file_path, auto_install=False):
    try:
        metadata, plugin_ids, collection = load_collection_file(file_path)
        if auto_install:
            kpm_plugin_id = "kangel_plugins_manager"
            if kpm_plugin_id in plugin_ids:
                plugin_ids.remove(kpm_plugin_id)
            
            if plugin_ids:
                def do_auto_install():
                    installed = 0
                    failed = 0
                    for plugin_id in plugin_ids:
                        try:
                            plugin_instance.install_plugin_by_id(plugin_id)
                            installed += 1
                        except Exception as e:
                            log(f"[KPM] Auto-install error for {plugin_id}: {e}")
                            failed += 1
                    
                    from ui.bulletin import BulletinHelper
                    if failed > 0:
                        BulletinHelper.show_info(_tr("auto_install_partial").format(installed, failed))
                    else:
                        BulletinHelper.show_success(_tr("auto_install_success").format(installed))
                
                from client_utils import run_on_queue
                run_on_queue(do_auto_install)
            else:
                from ui.bulletin import BulletinHelper
                BulletinHelper.show_info(_tr("auto_install_none"))
        else:
            plugin_instance._show_import_collection_designer(metadata, plugin_ids)
    except Exception as e:
        from ui.bulletin import BulletinHelper
        log(f"[KPM] Import collection error: {e}")
        BulletinHelper.show_error(_tr("collection_error").format(e))
