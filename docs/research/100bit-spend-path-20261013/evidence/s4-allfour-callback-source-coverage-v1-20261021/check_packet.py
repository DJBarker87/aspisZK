#!/usr/bin/env python3
import hashlib, json
from pathlib import Path
root=Path(__file__).resolve().parent
m=json.loads((root/"manifest.json").read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
expected={x["path"]:x for x in m["files"]}
actual={p.relative_to(root).as_posix():p for p in root.rglob("*") if p.is_file() and p.name not in ("manifest.json","SHA256SUMS","check_packet.py")}
assert set(expected)==set(actual), (set(expected)^set(actual))
for name,p in actual.items():
    assert sha(p)==expected[name]["sha256"], name
    assert p.stat().st_size==expected[name]["size_bytes"], name
for name,pin in m["direct_import_source_map"].items():
    src=root/pin["source"]
    assert src.exists(), name
    assert sha(src)==pin["source_sha256"], name
for module in m["modules"]:
    assert sha(root/module["source"])==module["source_sha256"]
    assert module["exit_status"]==0
print(f"PASS {len(actual)} files; {len(m['direct_import_source_map'])} direct source pins; {len(m['modules'])} green module(s)")
