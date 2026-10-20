#!/usr/bin/env python3
"""Mechanical shape/dataflow check for the extracted fission body adapter.
This checks the complete relevant control skeleton and field construction map;
Lean proves the Result/ControlFlow model separately. It does not prove the
Rust helper body or adoption into frozen finish_relation.
"""
import hashlib, json, pathlib, re, sys
root = pathlib.Path(__file__).resolve().parents[1]
funs = root / "extraction/fission-v1b/Funs.lean"
lean = root / "sources/FissionLoopStepSemanticsV1.lean"
mp = root / "extraction/body-adapter-map.json"
mapdata = json.loads(mp.read_text())

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
expected_funs = mapdata["generated_funs_sha256"]
assert sha(funs) == expected_funs, (sha(funs), expected_funs)
ft = funs.read_text()
lt = lean.read_text()
start = ft.index("def verifier.finish_round_loop_fission_loop.body")
end = ft.find("/--", start + 8)
body = ft[start:end if end >= 0 else len(ft)]
for token in [
    "core.iter.range.IteratorRange.next core.iter.range.StepUsize iter",
    "| none => ok (done (claim, none))",
    "verifier.finish_relation_round",
    "claim round",
    "core.result.Result.Insts.CoreOpsTry.branch r",
    "ControlFlow.Continue val",
    "ControlFlow.Break residual",
    "CoreOpsTryTraitFromResidualResultInfallible.from_residual",
    "ok (done (claim, some return_capture))",
]:
    assert token in body, f"generated body missing {token!r}"
for token in [
    "def assembledView", "variant := e.v1", "inactive := e.inactive",
    "folded_root := e.foldedRoot", "def assembledPrepared",
    "variant := e.v2", "roots := e.roots", "gamma := e.gamma",
    "kappa := e.kappa", "alpha := e.alpha", "rho := e.rho",
    "queries := e.queries", "semantic_alpha := e.semanticAlpha",
    "z := e.z", "claim := e.preparedClaim", "state := e.state",
    "def bodyAdapter", "IteratorRange.next core.iter.range.StepUsize iter",
    "step (assembledView env) (assembledPrepared env) claim round",
    "CoreOpsTry.branch r", "core.ops.control_flow.ControlFlow.Continue val",
    "core.ops.control_flow.ControlFlow.Break residual", "from_residual",
    "ok (done (claim, some return_capture))",
]:
    assert token in lt, f"Lean adapter missing {token!r}"
for forbidden in ["import AspisR1FinishRelationCurrent.FunsExternal", "import AspisR1FinishRelationCurrent.Funs"]:
    assert forbidden not in lt, f"forbidden direct generated/template import {forbidden!r}"
# Verify exact parameter-field coverage and ordering through the named records.
assert list(mapdata["mapping"]["view_update"].keys()) == ["v", "variant", "inactive", "folded_root"]
assert list(mapdata["mapping"]["prepared_fields"].keys()) == [
    "variant", "roots", "gamma", "kappa", "alpha", "rho", "queries",
    "semantic_alpha", "z", "claim", "state"
]
print(json.dumps({
    "status": "PASS",
    "generated_funs_sha256": sha(funs),
    "lean_adapter_sha256": sha(lean),
    "generated_body_sha256": hashlib.sha256(body.encode()).hexdigest(),
    "field_contracts": {k: len(v) for k,v in mapdata["mapping"].items() if isinstance(v, dict)},
    "limitation": "shape/dataflow check only; helper/source adoption remains open"
}, indent=2))
