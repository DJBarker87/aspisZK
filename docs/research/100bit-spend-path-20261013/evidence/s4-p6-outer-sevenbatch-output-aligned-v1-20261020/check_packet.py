from pathlib import Path
import hashlib,json
p=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
m=json.loads((p/"manifest.json").read_text())
assert m["schema"]=="focused-extractor-proof-packet-v1" and len(m["modules"])==3
for x in m["modules"]:
 for k in ["source","receipt","preflight","command","time_log","lean_log"]: assert (p/x[k]).is_file(),(x["name"],k)
 assert sha(p/x["source"])==x["source_sha256"]
 r=json.loads((p/x["receipt"]).read_text()); assert r["exit_status"]==0 and r["source_sha256"]==x["source_sha256"] and r["object_sha256"]==x["object_sha256"] and r["swaps"]==0
 assert x["axioms"]==["propext","Classical.choice","Quot.sound"]
for owner, imports in m["direct_import_source_map"].items():
 for n,d in imports.items():
  f=(p/d["source"]).resolve(); assert f.is_file(),(owner,n,str(f)); assert sha(f)==d["source_sha256"],(owner,n)
for n,d in m["inherited_owner_source_map"].items():
 f=(p/d["source"]).resolve(); assert f.is_file(),(n,str(f)); assert sha(f)==d["source_sha256"],n
assert not list(p.rglob("*.olean"))
print("PASS: source-only 3-module packet; exact source/object receipts, standard axioms, no binaries")
