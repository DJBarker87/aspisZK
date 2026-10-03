#!/usr/bin/env python3
"""Regenerate current source pins from the independent raw remote receipt."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
receipt = json.loads((ROOT / "lead-audit/remote-source-pins.stdout.json").read_text())
preflight_path = ROOT / "preflight.json"
preflight = json.loads(preflight_path.read_text())
files = receipt["files"]

rustc_keys = [
    "rustc_middle/src/mir/mod.rs",
    "rustc_middle/src/mir/basic_blocks.rs",
    "rustc_middle/src/mir/syntax.rs",
    "rustc_middle/src/mir/statement.rs",
    "rustc_middle/src/mir/terminator.rs",
    "rustc_span/src/lib.rs",
    "rustc_middle/src/mir/pretty.rs",
]
preflight["native_debug_source_sha256"] = {key: files[key]["sha256"] for key in rustc_keys}
preflight["source_pin_receipt"] = {
    "path": "lead-audit/remote-source-pins.stdout.json",
    "classification": receipt["classification"],
    "charon_revision": receipt["charon_revision"],
    "rustc_commit": "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65",
    "sha256": hashlib.sha256((ROOT / "lead-audit/remote-source-pins.stdout.json").read_bytes()).hexdigest(),
}
preflight["pinned_source"]["manifest_sha256"] = files["charon/Cargo.toml"]["sha256"]
preflight["pinned_source"]["lock_sha256"] = files["charon/Cargo.lock"]["sha256"]
preflight["pinned_source"]["toolchain_file_sha256"] = files["charon/rust-toolchain"]["sha256"]
preflight["selected_observer"]["source_sha256"] = files["charon/src/bin/charon-driver/translate/get_mir.rs"]["sha256"]
preflight["existing_release_artifacts"]["charon_wrapper"]["sha256_matches_top_level_bin_charon"] = files["charon/target/release/charon"]["sha256"]
preflight["existing_release_artifacts"]["top_level_bin_charon"]["sha256"] = files["bin/charon"]["sha256"]
preflight["existing_release_artifacts"]["charon_driver"]["sha256"] = files["charon/target/release/charon-driver"]["sha256"]
preflight_path.write_text(json.dumps(preflight, indent=2) + "\n")

# Rewrite receipt-overlapping entries in source-hashes.txt from the same data.
path_map = {
    "charon/Cargo.toml": "charon/Cargo.toml",
    "charon/Cargo.lock": "charon/Cargo.lock",
    "charon/rust-toolchain": "charon/rust-toolchain",
    "charon/src/bin/charon-driver/translate/get_mir.rs": "charon/src/bin/charon-driver/translate/get_mir.rs",
    "charon/src/bin/charon-driver/translate/translate_bodies.rs": "charon/src/bin/charon-driver/translate/translate_bodies.rs",
    "bin/charon": "bin/charon",
    "charon/target/release/charon": "charon/target/release/charon",
    "charon/target/release/charon-driver": "charon/target/release/charon-driver",
}
source_hashes = ROOT / "source-hashes.txt"
lines = source_hashes.read_text().splitlines()
for index, line in enumerate(lines):
    for label, receipt_key in path_map.items():
        if line.startswith(label + " SHA256 "):
            lines[index] = f"{label} SHA256 {files[receipt_key]['sha256']}"
for label in rustc_keys:
    lines = [f"{label} SHA256 {files[label]['sha256']}" if line.startswith(label + " SHA256 ") else line for line in lines]
source_hashes.write_text("\n".join(lines) + "\n")

# Fail closed on malformed hash fields and cross-file mismatch.
for key, item in files.items():
    value = item["sha256"]
    assert re.fullmatch(r"[0-9a-f]{64}", value), (key, value)
assert receipt["charon_revision"] == preflight["pinned_source"]["git_revision"]
for key in rustc_keys:
    assert preflight["native_debug_source_sha256"][key] == files[key]["sha256"]
for key in ("charon/Cargo.toml", "charon/Cargo.lock", "charon/rust-toolchain"):
    target = {"charon/Cargo.toml": "manifest_sha256", "charon/Cargo.lock": "lock_sha256", "charon/rust-toolchain": "toolchain_file_sha256"}[key]
    assert preflight["pinned_source"][target] == files[key]["sha256"]
for value in re.findall(r"SHA256 ([0-9a-f]+)", source_hashes.read_text()):
    assert re.fullmatch(r"[0-9a-f]{64}", value), value

def validate_sha_fields(value, path="$"):
    if isinstance(value, dict):
        for key, child in value.items():
            if "sha256" in key.lower() and isinstance(child, str):
                assert re.fullmatch(r"[0-9a-f]{64}", child), (path + "." + key, child)
            else:
                validate_sha_fields(child, path + "." + key)
    elif isinstance(value, list):
        for index, child in enumerate(value):
            validate_sha_fields(child, f"{path}[{index}]")
validate_sha_fields(preflight)
for line in source_hashes.read_text().splitlines():
    for key in rustc_keys:
        if line.startswith(key + " SHA256 "):
            assert line.endswith(files[key]["sha256"]), (line, files[key]["sha256"])
print(json.dumps({"result": "PASS", "receipt_file_count": len(files), "validated_hex_lengths": 64, "charon_revision": receipt["charon_revision"], "receipt_sha256": preflight["source_pin_receipt"]["sha256"]}, indent=2))
