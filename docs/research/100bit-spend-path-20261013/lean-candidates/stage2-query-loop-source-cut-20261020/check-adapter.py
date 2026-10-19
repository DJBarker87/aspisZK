from pathlib import Path
import re,json,hashlib
p=Path(__file__).resolve().parent
clean=lambda s:re.sub(r"^set_option (?:maxHeartbeats|maxRecDepth).*\n","",s,flags=re.M)
assert clean((p/"raw-generated/Types.lean").read_text())==(p/"sources/AspisR1Stage2QueryTailCut/Types.lean").read_text()
f=clean((p/"raw-generated/Funs.lean").read_text()).replace("import AspisR1Stage2QueryTailCut.FunsExternal\n","")
actual=(p/"sources/QueryTailExplicitQuery.lean").read_text()
q="""abbrev Query := Slice Std.U8 → verifier.Prepared → verifier.Accumulator →
  Array aspis_core.field.WideExact 29#usize → Option (verifier.Phase → Result Unit) →
  verifier.QueryGeometry → Option verifier.BatchedWeights →
  Result (core.result.Result Unit verifier.Error × verifier.Accumulator × Option verifier.BatchedWeights)

"""
f=f.replace("namespace AspisR1Stage2QueryTailCut\n","namespace AspisR1Stage2QueryTailCut\n\n"+q)
for n in ["verifier.candidate.tx2_query_tail_loop.body","verifier.candidate.tx2_query_tail_loop","verifier.candidate.tx2_query_tail"]:f=f.replace("def "+n+"\n","def "+n+"\n  (query : Query)\n")
f=f.replace("verifier.candidate.query_values proof","query proof").replace("verifier.candidate.tx2_query_tail_loop.body proof","verifier.candidate.tx2_query_tail_loop.body query proof").replace("verifier.candidate.tx2_query_tail_loop proof","verifier.candidate.tx2_query_tail_loop query proof")
assert f==actual
info=json.loads((p/"source-cut-check.json").read_text());base=(p/"rust-kit/fragments/stage2_tx2_common.rs").read_text();assert info["loop"] in base and info["loop"] in info["helper"]
assert hashlib.sha256(info["loop"].encode()).hexdigest()==info["loop_sha256"]
print("PASS byte-exact frozen loop statements and universally parameterized generated query boundary")
