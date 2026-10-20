#!/usr/bin/env python3
"""Parameterize the external operation boundary in exact generated Funs.

The adapter retains each Aeneas-generated function and loop body while threading
one explicit Ops record through generated internal calls. It strips only emitted
resource-option overrides and the axiom-template import.
"""
from pathlib import Path
import hashlib, json, re

HERE = Path(__file__).resolve().parent
RAW = HERE / "alternate-aeneas-v1/AspisR1FastDotsCurrent/Funs.lean"
OUT = HERE / "funs-v2/AspisR1FastDotsCurrent/FunsOpsV4.lean"
raw = RAW.read_text()

ops = '''/-- External source operations are explicit parameters, not axioms. -/
structure FourDotsOps where
  arrayFromFn : {T F : Type} → (N : Std.Usize) →
    core.ops.function.FnMut F Std.Usize T → F → Result (Array T N)
  wideLimbCount : Result Std.Usize
  wideAdd : aspis_core.field.wide_exact.WideExact →
    aspis_core.field.wide_exact.WideExact → Result aspis_core.field.wide_exact.WideExact
  wideFromLimbs : Array Std.U32 8#usize →
    Result (Option aspis_core.field.wide_exact.WideExact)
  wideToLimbs : aspis_core.field.wide_exact.WideExact →
    Result (Array Std.U32 8#usize)
  m31ReduceU64 : Std.U64 → Result aspis_core.field.M31
  m31FromBytes : Array Std.U8 4#usize → Result (Option aspis_core.field.M31)
  qm31FromBytes : Slice Std.U8 → Result (Option aspis_core.field.QM31)
  ebyKNew : Result fast_pairing.EbyKDot
  ebyKPush : fast_pairing.EbyKDot → aspis_core.field.wide_exact.WideExact →
    aspis_core.field.QM31 →
    Result ((core.result.Result Unit Unit) × fast_pairing.EbyKDot)
  ebyKFinish : fast_pairing.EbyKDot →
    Result aspis_core.field.wide_exact.WideExact

'''
external = {
    "core.array.from_fn": "ops.arrayFromFn",
    "aspis_core.field.wide_exact.WideExact.LIMB_COUNT": "ops.wideLimbCount",
    "aspis_core.field.wide_exact.WideExact.from_limbs": "ops.wideFromLimbs",
    "aspis_core.field.wide_exact.WideExact.to_limbs": "ops.wideToLimbs",
    "aspis_core.field.wide_exact.WideExact.add": "ops.wideAdd",
    "aspis_core.field.M31.reduce_u64": "ops.m31ReduceU64",
    "aspis_core.field.M31.from_le_bytes": "ops.m31FromBytes",
    "aspis_core.field.QM31.from_le_bytes": "ops.qm31FromBytes",
    "fast_pairing.EbyKDot.finish": "ops.ebyKFinish",
    "fast_pairing.EbyKDot.push": "ops.ebyKPush",
    "fast_pairing.EbyKDot.new": "ops.ebyKNew",
}

# Retain source body chunks by generated documentation boundaries.
lines=[]
for line in raw.splitlines():
    if line.startswith("set_option maxHeartbeats ") or line.startswith("set_option maxRecDepth "):
        continue
    if line.strip() == "import AspisR1FastDotsCurrent.FunsExternal":
        continue
    lines.append(line)
text="\n".join(lines)+"\n"
# Introduce explicit Ops record before generated declarations.
needle="namespace AspisR1FastDotsCurrent\n"
assert text.count(needle)==1
text=text.replace(needle,needle+"\n"+ops,1)

# Get names of all generated defs (including declarations with split `def` line).
# Enumerate all generated definitions, including one-line trait instances.
all_decls=list(re.finditer(r"(?m)^def(?:\s*\n\s*|\s+)([A-Za-z0-9_.]+)",text))
names=[m.group(1) for m in all_decls]
assert names, "no generated definitions found"
# Add an explicit Ops parameter to every definition, including one-line
# generated trait instance declarations.
for m in reversed(all_decls):
    pos=m.end()
    text=text[:pos]+"\n  (ops : FourDotsOps)"+text[pos:]

# Replace external names and pass `ops` to generated internal calls. Only text
# after each generated `:=` is treated as a body; headers/docs remain untouched.
chunks=re.split(r"(?=^/-- )",text,flags=re.M)
for i,chunk in enumerate(chunks):
    if ":=" not in chunk:
        continue
    head,body=chunk.split(":=",1)
    for old,new in sorted(external.items(),key=lambda kv:-len(kv[0])):
        body=re.sub(re.escape(old)+r"(?![A-Za-z0-9_.])",new,body)
    for name in sorted(names,key=len,reverse=True):
        body=re.sub(re.escape(name)+r"(?![A-Za-z0-9_.])",name+" ops",body)
    chunks[i]=head+":="+body
text="".join(chunks)
# Preserve the trait-instance argument as one expression when it is supplied to
# the higher-order from_fn operation; parentheses only disambiguate the adapter.
for instance in [
 "fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32",
 "fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact",
]:
    text=re.sub(r"(ops\.arrayFromFn [0-9]+#usize\s+)"+re.escape(instance)+r" ops",
                r"\1("+instance+r" ops)",text)

# Replace final audits with a clean explicit audit for the two public roots.
text=text.replace("\nend AspisR1FastDotsCurrent\n", "\n#print axioms fast_dots.four_dots\n#print axioms fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut\n\nend AspisR1FastDotsCurrent\n")
OUT.parent.mkdir(parents=True,exist_ok=True)
OUT.write_text(text)
manifest={
 "raw_generated_source":str(RAW.relative_to(HERE)),
 "raw_generated_sha256":hashlib.sha256(RAW.read_bytes()).hexdigest(),
 "adapted_source":str(OUT.relative_to(HERE)),
 "adapted_sha256":hashlib.sha256(OUT.read_bytes()).hexdigest(),
 "generated_functions_parameterized":names,
 "external_calls_parameterized":external,
 "generated_resource_options_removed":["maxHeartbeats","maxRecDepth"],
 "external_template_import_removed":True,
 "body_transform":"Exact generated body retained after substitutions of 11 external operation constants by `ops` fields and threading `ops` through generated internal calls; source checker required before proof interpretation.",
 "source_scope":"No semantic operation laws are asserted. The adapter is a generic control-flow model over explicit operations."
}
(HERE/"funs-adapter-v4-manifest.json").write_text(json.dumps(manifest,indent=2)+"\n")
print(json.dumps(manifest,indent=2))
