from pathlib import Path
import hashlib,json,sys
r=Path(__file__).resolve().parent
m=json.loads((r/"manifest.json").read_text())
assert m["schema"]=="focused-extractor-proof-packet-v1"
for mod in m["modules"]:
 p=r/mod["source"]; assert hashlib.sha256(p.read_bytes()).hexdigest()==mod["source_sha256"]
 q=r/mod["receipt"]; assert hashlib.sha256(q.read_bytes()).hexdigest()==mod["receipt_sha256"]
 rec=json.loads(q.read_text()); assert rec["exit_status"]==0 and rec["object_sha256"]==mod["object_sha256"]
 assert rec["source_sha256"]==mod["source_sha256"]
for n,pin in m["direct_import_source_map"].items():
 p=r/pin["path"]; assert hashlib.sha256(p.read_bytes()).hexdigest()==pin["source_sha256"]
for p in r.rglob("*"):
 assert p.suffix not in {".olean",".ilean",".ir",".llbc"}, p
print("ordinary callback packet: source, receipt, and no-binary checks passed")
