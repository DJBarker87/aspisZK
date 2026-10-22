#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
r=Path(__file__).resolve().parent;m=json.loads((r/"manifest.json").read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
e={x["path"]:x for x in m["files"]};a={p.relative_to(r).as_posix():p for p in r.rglob("*") if p.is_file() and p.name not in ("manifest.json","SHA256SUMS","check_packet.py")}
assert set(e)==set(a),(set(e)^set(a))
for n,p in a.items():assert sha(p)==e[n]["sha256"] and p.stat().st_size==e[n]["size_bytes"],n
for mod,pin in m["direct_import_source_map"].items():assert sha(r/pin["source"])==pin["source_sha256"],mod
for x in m["modules"]:assert sha(r/x["source"])==x["source_sha256"] and x["exit_status"]==0
print(f"PASS {len(a)} files; {len(m['direct_import_source_map'])} direct imports; {len(m['modules'])} green module(s)")
