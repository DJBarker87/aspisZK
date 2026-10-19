from pathlib import Path
import json,re,hashlib
p=Path(__file__).resolve().parent
clean=lambda s:re.sub(r"^set_option (?:maxHeartbeats|maxRecDepth).*\n","",s,flags=re.M)
assert clean((p/"raw-generated/Types.lean").read_text())==(p/"sources/AspisR1Post25Transcript/Types.lean").read_text()
f=clean((p/"raw-generated/Funs.lean").read_text()).replace("import AspisR1Post25Transcript.FunsExternal\n","")
ops="""structure SamplerOps where
  gamma : Array U8 32#usize → Result aspis_core.field.WideExact
  ordinary : Array U8 32#usize → Result aspis_core.field.WideExact
  qm31 : Array U8 32#usize → Result aspis_core.field.QM31
  embed : aspis_core.field.QM31 → Result aspis_core.field.WideExact

"""
f=f.replace("namespace AspisR1Post25Transcript\n","namespace AspisR1Post25Transcript\n\n"+ops)
for n in ["transcript.Transcript.scalar","transcript.Transcript.scalar_k"]:f=f.replace("def "+n+"\n","def "+n+"\n  (ops : SamplerOps)\n")
f=f.replace("sampler.gamma_sample block","ops.gamma block").replace("sampler.ordinary_sample block","ops.ordinary block").replace("sampler.qm31_sample a","ops.qm31 a").replace("aspis_core.field.WideExact.from_qm31 out","ops.embed out")
assert f==(p/"sources/Post25TranscriptExplicitSamplers.lean").read_text()
info=json.loads((p/"frozen-source-pins.json").read_text())
for item in info["functions"]:
 assert hashlib.sha256(item["source_text"].encode()).hexdigest()==item["sha256"]
 assert item["source_text"] in (p/"rust-kit/lib.rs").read_text()
print("PASS unchanged generated control/frames under explicit sampler parameterization; frozen source body pins")
