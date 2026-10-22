from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parent
m=json.loads((R/"manifest.json").read_text())
assert m["compiled_objects_included"] is False and m["binaries_included"] is False
assert subprocess.run([sys.executable,str(R/"check_sourcecut.py")],check=False).returncode==0
assert subprocess.run([sys.executable,str(R/"check_declaration_inventory.py")],check=False).returncode==0
sha=lambda b:hashlib.sha256(b).hexdigest()
for x in m["files"]:
 b=(R/x["path"]).read_bytes(); assert len(b)==x["bytes"] and sha(b)==x["sha256"],x["path"]
inventory=json.loads((R/"evidence/charon/declaration-inventory.json").read_text())
assert inventory["llbc_sha256"]==m["charon_llbc_sha256"] and inventory["has_errors"] is False
assert inventory["function_count"]>0 and inventory["type_count"]>0
source=(R/"input/src/field/wide_exact.rs").read_text()
assert "pub fn mul(self, rhs: Self) -> Self" in source
lean=(R/"evidence/aeneas/generated/AspisR1S9ActualWideMulCutV1/Funs.lean").read_text()
assert "def field.wide_exact.WideExact.mul" in lean and "def focused_wide_exact_mul" in lean
for ph in ("charon","aeneas"):
 r=json.loads((R/f"evidence/{ph}/receipt.json").read_text())
 assert r["exit_status"]==0 and not r["timed_out"] and r["swap_current_bytes"]==0
 assert r["limits"]=={"memory.high":"2147483648","memory.max":"4294967296","memory.swap.max":"0"}
 assert (R/f"evidence/admission-{ph}/admission.json").exists()
print("S9 WideExact.mul source-cut evidence: PASS")
