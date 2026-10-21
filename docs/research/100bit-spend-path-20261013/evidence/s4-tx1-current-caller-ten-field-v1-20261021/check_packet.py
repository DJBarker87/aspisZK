from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parent; ROOT=D.parents[4]; sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest(); m=json.loads((D/"manifest.json").read_text())
assert m["schema"]=="focused-extractor-proof-packet-v1"
for f in m["files"]:
 p=D/f["path"]; assert p.is_file() and sha(p)==f["sha256"] and p.stat().st_size==f["size_bytes"],f["path"]
mod=m["modules"][0]; r=json.loads((D/mod["receipt"]).read_text()); p=json.loads((D/mod["preflight"]).read_text()); cmd=json.loads((D/mod["command"]).read_text())
assert r["exit_status"]==0 and r["watchdog_abort"] is None and r["process_swaps"]==0
assert r["source_sha256"]==mod["source_sha256"]==sha(D/mod["source"]) and r["object_sha256"]==mod["object_sha256"]
assert r["source_revision_at_launch"]==mod["source_revision"]==m["source_revision_at_launch"]
assert r["peak_aggregate_rss_bytes"]==mod["peak_aggregate_rss_bytes"]<8*2**30 and r["wall_seconds"]==mod["wall_seconds"]
assert p["lean_sha256"]==m["compiler"]["sha256"] and p["lean"]==m["compiler"]["path"]
assert p["lean_path_sha256"]==m["lean_path_sha256"]==sha(D/m["lean_path_source"])
launched=next(x.split("=",1)[1] for x in cmd["argv"] if x.startswith("LEAN_PATH="))
assert launched== (D/m["launch_lean_path_source"]).read_text().rstrip("\n")
assert sha(D/m["launch_lean_path_source"])==m["launch_lean_path_sha256"]
for name,x in m["direct_import_source_map"].items():
 src=(ROOT/x["source"]).resolve(); rr=json.loads((ROOT/x["receipt"]).read_text())
 assert src.is_file() and sha(src)==x["source_sha256"]==rr.get("source_sha256")
 assert x["object_sha256"]==rr.get("object_sha256")
 assert rr.get("exit_status",rr.get("exit_code"))==0, name
log=(D/"evidence/lean.log").read_text(); reports=re.findall(r"depends on axioms:\s*\[([^]]*)\]",log)
assert len(reports)==1 and set(re.findall(r"[A-Za-z_][A-Za-z_0-9.]*",reports[0]))=={"propext","Classical.choice","Quot.sound"}
assert "sorryAx" not in log and "error:" not in log
print("PASS: current-caller ten-field consumer; exact actual-carrier maps; standard axioms")
