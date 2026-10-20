from pathlib import Path
import re,json,hashlib
p=Path(__file__).resolve().parent
raw=(p/"raw-generated/Funs.lean").read_text()
f=re.sub(r"^set_option (?:maxHeartbeats|maxRecDepth).*\n","",raw,flags=re.M)
f=f.replace("import AspisR1WeightsFieldCurrent.Types\n","").replace("import AspisR1WeightsFieldCurrent.FunsExternal\n","")
f=f.replace("def weights.field\n","def weights.field\n  {T : Type} (decode : Slice Std.U8 → Result (Option T))\n")
f=f.replace("Result aspis_core.field.WideExact","Result T").replace("aspis_core.field.WideExact.from_le_bytes s","decode s")
assert f==(p/"sources/WeightsFieldExplicitDecoder.lean").read_text()
info=json.loads((p/"frozen-source.json").read_text())
assert hashlib.sha256(info["function"].encode()).hexdigest()==info["function_sha256"]
assert (p/"rust-kit/lib.rs").read_text().count(info["function"])==1
opacity=json.loads((p/"extraction/boundary-opacity-check.json").read_text())
assert opacity[0]["body_kind"]==["Structured"] and opacity[0]["source_text"]==info["function"]
assert opacity[1]["body_kind"]=="Opaque"
print("PASS: exact source selector; generated body preserved under universal explicit decoder/type parameterization")
