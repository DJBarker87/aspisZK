#!/usr/bin/env python3
"""Validate source/object pins and the read-only S4 OLean-header preflight."""
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE / "manifest.json").read_text())

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

errors = []
for module, rec in manifest["roots"].items():
    for field, expected in (("source_path", rec["source_sha256"]), ("object_path", rec["object_sha256"]),
                            ("receipt_or_manifest_path", rec["receipt_or_manifest_sha256"]),
                            ("command_path", rec["command_sha256"]), ("profile_path", rec["profile_sha256"])):
        p = Path(rec[field])
        if not p.is_file():
            errors.append(f"{module}: missing {field}: {p}")
        elif sha(p) != expected:
            errors.append(f"{module}: {field} SHA mismatch: {p}")
    if not rec["source_pin_match"] or not rec["object_pin_match"]:
        errors.append(f"{module}: producer receipt does not match current source/object")

owners = json.loads((HERE / "selected-owners.json").read_text())
closure = json.loads((HERE / "aggregate-closure.json").read_text())
profile = (HERE / "LEAN_PATH.txt").read_text().strip()
if sha(HERE / "LEAN_PATH.txt") != manifest["combined_profile"]["sha256"]:
    errors.append("combined LEAN_PATH hash mismatch")
if any(not Path(p).is_dir() for p in profile.split(":")):
    errors.append("combined LEAN_PATH contains a missing directory")
if closure["missing"]:
    errors.append(f"unresolved imports: {closure['missing']}")
if len(closure["owners"]) != manifest["closure_walk"]["modules"]:
    errors.append("closure owner count mismatch")
for module, rec in manifest["roots"].items():
    own = closure["owners"].get(module)
    if not own or own["sha256"] != rec["object_sha256"]:
        errors.append(f"{module}: selected closure owner mismatch")
for module, own in closure["owners"].items():
    table = owners.get(module)
    if not table or table["sha256"] != own["sha256"] or table["object_path"] != own["path"]:
        errors.append(f"selected-owner table mismatch: {module}")
for check in manifest["new_roots_direct_dependency_pin_checks"]:
    if not check["match"]:
        errors.append(f"new direct pin mismatch: {check['packet']} / {check['module']}")
for group, checks in manifest["historical_direct_import_pins"].items():
    for check in checks:
        if not check["match"]:
            errors.append(f"historical direct pin mismatch: {group} / {check['module']}")
for name, rec in manifest["source_and_producer_packets"].items():
    if not Path(rec["path"]).is_file() or sha(rec["path"]) != rec["sha256"]:
        errors.append(f"producer manifest mismatch: {name}")
for module in manifest["historical_unhashed_tx2_modules_now_pinned"]:
    owner = closure["owners"].get(module["module"])
    if not owner or owner["sha256"] != module["selected_sha256"]:
        errors.append(f"previously unhashed module not pinned: {module['module']}")
if not manifest["additional_selected_owner"]["selected_owner_matches"]:
    errors.append("CurrentPreparedInstalledMeaning selected owner mismatch")
meaning = manifest["additional_selected_owner"]
if sha(meaning["source_path"]) != meaning["source_sha256"] or sha(meaning["object_path"]) != meaning["object_sha256"]:
    errors.append("CurrentPreparedInstalledMeaning source/object SHA mismatch")
policy = manifest["source_policy_note"]
if sha(policy["source_path"]) != policy["source_sha256"] or sha(policy["path"]) != policy["sha256"]:
    errors.append("source-policy pin mismatch")
if any(p.suffix == ".olean" for p in HERE.rglob("*")):
    errors.append("compiled object unexpectedly copied into packet")
for rel, expected in manifest.get("packet_file_hashes", {}).items():
    fp = HERE / rel
    if not fp.is_file() or sha(fp) != expected:
        errors.append(f"packet file SHA mismatch: {rel}")
if manifest["summary"]["final_replay_performed"]:
    errors.append("manifest incorrectly claims a final replay")
if errors:
    print("FAIL")
    print("\n".join(errors))
    sys.exit(1)
print(f"PASS: {len(closure['owners'])} owner pins; 7 roots; zero unresolved imports; no OLean files in packet")
