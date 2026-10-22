from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((D/"manifest.json").read_text())
for f in m["files"]: assert sha(D/f["path"])==f["sha256"],f["path"]
for name,pin in m["direct_import_source_map"].items():
 assert sha(D/pin["source"])==pin["source_sha256"],name
r=json.loads((D/"evidence/receipt.json").read_text()); p=json.loads((D/"evidence/preflight.json").read_text()); c=json.loads((D/"evidence/command.json").read_text())
mod=m["modules"][0]
assert r["exit_status"]==0 and r["watchdog_abort"] is None and r["process_swaps"]==0
assert r["source_sha256"]==mod["source_sha256"]==sha(D/mod["source"])
assert r["object_sha256"]==mod["object_sha256"] and r["source_revision_at_launch"]==mod["source_revision"]
assert r["peak_aggregate_rss_bytes"]<8*2**30 and r["peak_process_rss_bytes"]<8*2**30
assert c["argv"][c["argv"].index("-M")+1]=="4400" and "-j1" in c["argv"]
assert p["lean"]==m["compiler"]["path"] and p["lean_sha256"]==m["compiler"]["sha256"]
assert sha(D/"evidence/LEAN_PATH.txt")==m["launch"]["lean_path_sha256"]
log=(D/"evidence/lean.log").read_text(); assert "error:" not in log and "sorryAx" not in log
a=re.findall(r"depends on axioms:\s*\[([^]]*)\]",log); assert len(a)==1
assert set(re.findall(r"[A-Za-z_][A-Za-z_0-9.]*",a[0])) <= {"propext","Classical.choice","Quot.sound"}
s=(D/mod["source"]).read_text(); assert not re.search(r"\b(sorry|axiom|native_decide)\b",s)
assert not any(x.suffix in {".olean",".ilean",".ir",".o",".llbc"} for x in D.rglob("*") if x.is_file())
print("PASS: S4 returned-model transport packet; authentication and source-index geometry remain upstream")
