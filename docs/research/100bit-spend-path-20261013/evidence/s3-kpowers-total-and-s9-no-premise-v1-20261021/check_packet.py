#!/usr/bin/env python3
import hashlib,json,pathlib
r=pathlib.Path(__file__).resolve().parent; m=json.loads((r/"manifest.json").read_text())
assert m["schema"]=="focused-extractor-proof-packet-v1"
for rel,x in m["files"].items():
 p=r/rel; assert p.is_file(),rel; b=p.read_bytes(); assert len(b)==x["bytes"] and hashlib.sha256(b).hexdigest()==x["sha256"],rel
for name,x in m["direct_import_source_map"].items():
 p=r/x["source"]; assert p.is_file(),name; assert hashlib.sha256(p.read_bytes()).hexdigest()==x["source_sha256"],name
for x in m["modules"]:
 p=r/x["source"]; assert hashlib.sha256(p.read_bytes()).hexdigest()==x["source_sha256"]
 assert x["exit_status"]==0 and x["swap_bytes"]==0
 assert set(x["axioms"])<={"propext","Classical.choice","Quot.sound"}
print("source-only kpowers/S9 packet PASS")
