#!/usr/bin/env python3
"""Build the S4 Lean adapter from exact Aeneas output.

Only generated resource-limit commands/importing the axiom template are removed;
external operation identifiers are replaced with explicitly quantified operation
parameters. The generated function/loop declaration bodies otherwise remain byte
identical after those deterministic substitutions.
"""
from pathlib import Path
import hashlib, json

HERE = Path(__file__).resolve().parent
RAW = HERE / "alternate-aeneas-v1/AspisR1FastDotsCurrent/Funs.lean"
OUT = HERE / "funs/AspisR1FastDotsCurrent/Funs.lean"
MANIFEST = HERE / "funs-adapter-manifest.json"
raw = RAW.read_text()

# These are the generated external call sites. Their implementations are boundary
# parameters, never axioms in this adapter.
replacements = {
    "core.array.from_fn": "opArrayFromFn",
    "aspis_core.field.wide_exact.WideExact.LIMB_COUNT": "opWideLimbCount",
    "aspis_core.field.wide_exact.WideExact.from_limbs": "opWideFromLimbs",
    "aspis_core.field.wide_exact.WideExact.to_limbs": "opWideToLimbs",
    "aspis_core.field.wide_exact.WideExact.add": "opWideAdd",
    "aspis_core.field.M31.reduce_u64": "opM31ReduceU64",
    "aspis_core.field.M31.from_le_bytes": "opM31FromBytes",
    "aspis_core.field.QM31.from_le_bytes": "opQM31FromBytes",
    "fast_pairing.EbyKDot.finish": "opEbyKFinish",
    "fast_pairing.EbyKDot.push": "opEbyKPush",
    "fast_pairing.EbyKDot.new": "opEbyKNew",
}
# Remove only generated heartbeat/depth overrides and the template import.
lines = raw.splitlines()
kept = []
for line in lines:
    if line.startswith("set_option maxHeartbeats ") or line.startswith("set_option maxRecDepth "):
        continue
    if line.strip() == "import AspisR1FastDotsCurrent.FunsExternal":
        continue
    kept.append(line)
text = "\n".join(kept) + "\n"

block = '''\n/-- Explicit operation boundary replacing generated external-template axioms. -/
variable
  (opArrayFromFn : {T F : Type} → (N : Std.Usize) →
    core.ops.function.FnMut F Std.Usize T → F → Result (Array T N))
  (opWideLimbCount : Result Std.Usize)
  (opWideAdd : aspis_core.field.wide_exact.WideExact →
    aspis_core.field.wide_exact.WideExact → Result aspis_core.field.wide_exact.WideExact)
  (opWideFromLimbs : Array Std.U32 8#usize →
    Result (Option aspis_core.field.wide_exact.WideExact))
  (opWideToLimbs : aspis_core.field.wide_exact.WideExact →
    Result (Array Std.U32 8#usize))
  (opM31ReduceU64 : Std.U64 → Result aspis_core.field.M31)
  (opM31FromBytes : Array Std.U8 4#usize → Result (Option aspis_core.field.M31))
  (opQM31FromBytes : Slice Std.U8 → Result (Option aspis_core.field.QM31))
  (opEbyKNew : Result fast_pairing.EbyKDot)
  (opEbyKPush : fast_pairing.EbyKDot → aspis_core.field.wide_exact.WideExact →
    aspis_core.field.QM31 →
    Result ((core.result.Result Unit Unit) × fast_pairing.EbyKDot))
  (opEbyKFinish : fast_pairing.EbyKDot →
    Result aspis_core.field.wide_exact.WideExact)
'''
needle = "namespace AspisR1FastDotsCurrent\n"
assert text.count(needle) == 1
text = text.replace(needle, needle + block, 1)
for old, new in sorted(replacements.items(), key=lambda kv: -len(kv[0])):
    text = text.replace(old, new)
OUT.parent.mkdir(parents=True, exist_ok=True)
OUT.write_text(text)
manifest = {
    "raw_generated_source": str(RAW.relative_to(HERE)),
    "raw_generated_sha256": hashlib.sha256(RAW.read_bytes()).hexdigest(),
    "adapted_source": str(OUT.relative_to(HERE)),
    "adapted_sha256": hashlib.sha256(OUT.read_bytes()).hexdigest(),
    "removed_generated_resource_option_prefixes": ["set_option maxHeartbeats", "set_option maxRecDepth"],
    "removed_import": "AspisR1FastDotsCurrent.FunsExternal",
    "external_replacements": replacements,
    "preserved_declaration_spans": "All generated declaration bodies retained; only each external call symbol is substituted by its explicit section parameter.",
    "remaining_correspondence": "The operation parameters require source-specific semantic instantiation; this adapter alone proves only the emitted control-flow structure parametrically."
}
MANIFEST.write_text(json.dumps(manifest, indent=2) + "\n")
print(json.dumps(manifest, indent=2))
