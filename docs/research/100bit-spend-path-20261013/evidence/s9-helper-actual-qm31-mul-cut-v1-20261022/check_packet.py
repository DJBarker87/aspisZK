from pathlib import Path
import hashlib, json
ROOT=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((ROOT/"manifest.json").read_text())
assert m["schema"]=="source-cut-evidence-packet-v1"
for rel,h in m["files"].items():
 p=ROOT/rel; assert p.is_file(),rel; assert sha(p)==h,rel
ids=json.loads((ROOT/"source-identities.json").read_text())
repo=ROOT.parents[4]
for key,rel in (("actual_core_field","input/src/field.rs"),("actual_core_wide_exact","input/src/field/wide_exact.rs")):
 assert sha(ROOT/rel)==ids[key]["sha256"]
 assert sha(repo/ids[key]["path"])==ids[key]["sha256"]
rc=json.loads((ROOT/"runs-charon/receipt.json").read_text()); ra=json.loads((ROOT/"runs-aeneas/receipt.json").read_text())
for r in (rc,ra):
 assert r["exit_status"]==0 and r["timed_out"] is False
 assert r["limits"]=={"memory.high":"2147483648","memory.max":"4294967296","memory.swap.max":"0"}
 assert r["swap_current_bytes"]==0 and "oom_kill 0" in r["memory_events_after"] and r["cgroup"] and r["argv"]
assert rc["start_from"]==["crate::focused_qm31_mul","crate::field::QM31::mul"]
assert "QM31" in " ".join(rc["start_from"])
assert ra["llbc_sha256"]==rc["llbc_sha256"]
assert ra["transparent_target_declarations"]["QM31.mul"][0]=="Transparent"
for n in ("CM31.mul","CM31.add","CM31.sub","mul_by_r","M31.mul","M31.sub","M31.add","reduce_u64"):
 assert ra["transparent_target_declarations"][n][0]=="Transparent",n
assert json.loads((ROOT/"llbc-summary.json").read_text())["raw_llbc_sha256"]==rc["llbc_sha256"]
for p in ROOT.rglob("*"):
 if p.is_file(): assert p.suffix not in (".llbc",".olean",".ilean",".pyc"),p
print("attempt19 actual QM31 source-cut packet checks: PASS")
