from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
m=json.loads((R/"manifest.json").read_text())
assert m["schema"]=="focused-extractor-proof-packet-v1"
assert m["compiled_objects_included"] is False and m["raw_llbc_included"] is False
for rel,h in m["files_sha256"].items():assert sha((R/rel).read_bytes())==h,rel
for f in R.rglob("*"):
 if f.is_file():assert f.suffix not in {".llbc",".olean",".ilean",".ir",".so",".dylib",".dll"},str(f)
ident=json.loads((R/"source-identities.json").read_text())
for rel,v in ident["cut_files"].items():assert sha((R/rel).read_bytes())==v["sha256"],rel
assert (R/"input/src/field.rs").read_bytes()==(R/"source-snapshots/field.rs").read_bytes()
assert (R/"input/src/field/wide_exact.rs").read_bytes()==(R/"source-snapshots/wide_exact.rs").read_bytes()
cr=json.loads((R/"evidence/charon/receipt.json").read_text()); ar=json.loads((R/"evidence/aeneas/receipt.json").read_text())
inv=json.loads((R/"evidence/charon/declaration-inventory.json").read_text()); val=json.loads((R/"evidence/aeneas/validation-correction.json").read_text())
assert cr["exit_status"]==0 and ar["exit_status"]==0 and not ar["timed_out"]
assert cr["llbc_sha256"]==ar["llbc_sha256"]==m["raw_llbc_sha256"]==inv["llbc_sha256"]
assert ar["limits"]=={"memory.high":"2147483648","memory.max":"4294967296","memory.swap.max":"0"}
assert val["validation_status"]=="PASS" and val["all_generated_field_functions_nonopaque"] is True
assert set(val["target_functions"])=={"QM31.square","WideExact.mul_qm31"}
assert val["generated_field_function_count"]==17
assert "fully-qualified" in (R/"post-run-checker-diagnostic.md").read_text()
print("Aeneas source-only packet: PASS")
