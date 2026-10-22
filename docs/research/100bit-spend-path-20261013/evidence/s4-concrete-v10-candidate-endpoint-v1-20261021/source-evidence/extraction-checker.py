#!/usr/bin/env python3
"""Check the retained v10 extraction receipt and executable-body identity."""
from pathlib import Path
import hashlib, json, re

HERE = Path(__file__).resolve().parent
E = HERE / "evidence"
V10 = E / "generated/AspisR1FastDotsMinimalFixedCallsV10/Funs.lean"
V6 = HERE.parent.parent / "s4-four-dots-fixed-call-v2/sources/FourDotsFixedV6-Funs.lean"

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def executable_body(path, name):
    text = path.read_text()
    match = re.search(
        r"^def " + re.escape(name) + r"\n.*?\n  := do\n(.*?)(?=^/--|^end |\Z)",
        text, re.M | re.S)
    assert match, f"missing generated definition {name} in {path}"
    return match.group(1).rstrip()

assert sha(E / "four_dots.llbc") == "da5a61fddb4d82bb2684220cd8923ae1e21f647341c13aa1afdaf60f2314b7ef"
assert sha(V10) == "089f0ec1a9e03a7044756f8f42f27f8b7eaf06d5a0b4996a738b14b987c83975"
assert sha(V6) == "38276aed2316117b0b17d492f2e1e9894de1cce0e8c2db306ddf34bae011c760"

outer_v10 = executable_body(V10, "fast_dots.four_dots")
outer_v6 = executable_body(V6, "fast_dots.four_dots_fixed")
helper_v10 = executable_body(V10, "fast_dots.four_dots_one")
helper_v6 = executable_body(V6, "fast_dots.four_dots_one")
assert outer_v10 == outer_v6, "v10 extracted outer executable body differs from v6 fixed-call body"
assert helper_v10 == helper_v6, "v10 extracted helper executable body differs from v6 helper"
assert "from_fn" not in outer_v10 and "array.from_fn" not in outer_v10
for i, binding in enumerate(("we", "we1", "we2", "we3")):
    assert f"let {binding} ← fast_dots.four_dots_one q1 g {i}#usize" in outer_v10
assert "ok (Array.make 4#usize [ we, we1, we2, we3 ])" in outer_v10

charon = json.loads((E / "runs-charon-retry5/receipt.json").read_text())
aeneas = json.loads((E / "runs-aeneas-retry6/receipt.json").read_text())
assert charon["exit_status"] == 0 and not charon["timed_out"]
assert aeneas["exit_status"] == 0 and not aeneas["timed_out"]
assert charon["outputs"]["four_dots.llbc"] == sha(E / "four_dots.llbc")
assert aeneas["outputs"]["generated/AspisR1FastDotsMinimalFixedCallsV10/Funs.lean"] == sha(V10)
# The focused accepted-run helper join is a separate Lean theorem packet.
JOIN = E / "tail-literal-run-join-v1"
JOIN_SOURCE = JOIN / "sources/S4TailLiteralJoinV1.lean"
JOIN_RECEIPT = json.loads((JOIN / "receipt.json").read_text())
JOIN_PREFLIGHT = json.loads((JOIN / "preflight.json").read_text())
assert sha(JOIN_SOURCE) == "7b944df0dd62d027ade6401a769dca06cae4887427aba40b29e479a301f3e442"
assert JOIN_RECEIPT["exit_status"] == 0
assert JOIN_RECEIPT["source_sha256"] == sha(JOIN_SOURCE)
assert JOIN_RECEIPT["object_sha256"] == "36f4816ab19747b1d3c5521b8d405030e6550f9470d8cb27f6d1d64bc256c8ca"
assert JOIN_RECEIPT["swaps"] == 0 and JOIN_RECEIPT["wall_seconds"] == 26.09
assert JOIN_PREFLIGHT["direct_imports"]["S4TailLoopForwardRootV1"]["source_sha256"] == "069abef23081726625592f605cfd222aa2a03a289a263827f14283028caa3c7e"
assert JOIN_PREFLIGHT["direct_imports"]["S4TailLoopForwardRootV1"]["object_sha256"] == "4a8897e16a575345f2c463f79a5b9e1ab7c2f7b052eaa8bc5c77f6590e985cff"
assert JOIN_RECEIPT["axioms"] == ["propext", "Classical.choice", "Quot.sound"]
# Full-MIR original-source probe: default S4 selection is opaque; explicit includes
# expose the current core array constructors in LLBC, though Aeneas still fails earlier.
FULL = E / "full-mir-original-fromfn-v1"
EXP = E / "full-mir-original-fromfn-explicit-includes-v1"
LLBC0 = FULL / "artifacts/four_dots.llbc"
LLBC1 = EXP / "artifacts/four_dots.llbc"
AUDIT0 = json.loads((FULL / "llbc-audit.json").read_text())
AUDIT1 = json.loads((EXP / "llbc-audit.json").read_text())
assert sha(LLBC0) == "858de3542c4c331bb8c76651505cdeacf2f5dc314a40ca5263e4fab48e8491f7"
assert sha(LLBC1) == "8dda114efb68e46c0014116a9d5de96dde34cd40b3b27595f54a455bc96c51c8"
assert AUDIT0["has_errors"] is False and AUDIT1["has_errors"] is False
assert any(x["name"] == "core::array::from_fn" and x["body_kind"] == "Opaque" and x["opacity"] == "Foreign" for x in AUDIT0["selected_functions"])
assert any(x["name"] == "core::array::from_fn" and x["body_kind"] == "Structured" and x["opacity"] == "Transparent" for x in AUDIT1["array_and_iterator_functions"])
assert any(x["name"] == "core::array::try_from_fn" and x["body_kind"] == "Structured" and x["opacity"] == "Transparent" for x in AUDIT1["array_and_iterator_functions"])
assert any(x["name"] == "core::array::try_from_fn_erased" and x["body_kind"] == "Structured" and x["opacity"] == "Transparent" for x in AUDIT1["array_and_iterator_functions"])
assert any(x["name"] == "core::array::Guard::<impl>::drop_glue" and x["opacity"] == "Foreign" for x in AUDIT1["array_and_iterator_functions"])
assert "--sysroot" not in json.loads((EXP / "artifacts/runs-charon/command.json").read_text())
assert "--include" in json.loads((EXP / "artifacts/runs-charon/command.json").read_text())
control_log = (FULL / "artifacts/runs-aeneas/stdout.log").read_text()
assert "lines 29:16-31:17" in control_log and "Internal error" in control_log
explicit_receipt = json.loads((EXP / "artifacts/runs-aeneas/receipt.json").read_text())
assert explicit_receipt["exit_status"] == 2 and not explicit_receipt["timed_out"]
assert explicit_receipt["outputs"]["four_dots.llbc"] == sha(LLBC1)
explicit_log = (EXP / "artifacts/runs-aeneas/stdout.log").read_text()
assert "Nested-loop returns require exactly one Option language item" in explicit_log
assert "core/src/array/mod.rs" in explicit_log and "906:0-909:29" in explicit_log
NO_MONO = E / "full-mir-original-fromfn-explicit-includes-no-monomorphize-v1"
LLBC2 = NO_MONO / "artifacts/four_dots.llbc"
AUDIT2 = json.loads((NO_MONO / "llbc-audit.json").read_text())
assert sha(LLBC2) == "872cf014cbf3cd26341d4ea2d973352768cd66bc75943b3f6e6cb295962ecd41"
assert AUDIT2["has_errors"] is False and AUDIT2["option_lang_item_count"] == 1
assert [x["def_id"] for x in AUDIT2["option_lang_items"]] == [6]
assert all(any(x["name"] == name and x["body_kind"] == "Structured" and x["opacity"] == "Transparent" for x in AUDIT2["array_and_iterator_functions"]) for name in ("core::array::from_fn", "core::array::try_from_fn", "core::array::try_from_fn_erased"))
no_mono_charon = json.loads((NO_MONO / "artifacts/runs-charon/receipt.json").read_text())
no_mono_aeneas = json.loads((NO_MONO / "artifacts/runs-aeneas/receipt.json").read_text())
assert no_mono_charon["exit_status"] == 0 and no_mono_aeneas["exit_status"] == 2
assert no_mono_charon["outputs"]["four_dots.llbc"] == sha(LLBC2)
assert no_mono_aeneas["outputs"]["four_dots.llbc"] == sha(LLBC2)
no_mono_log = (NO_MONO / "artifacts/runs-aeneas/stdout.log").read_text()
assert "lines 29:16-31:17" in no_mono_log and "Internal error" in no_mono_log
assert no_mono_aeneas["limits"]["memory.swap.max"] == "0"
prepass = json.loads((NO_MONO / "aeneas-option-prepass-source-pin.json").read_text())
assert prepass["source_sha256"] == "b21a08dcfc2c59ba867a1dfe76c7eddd5af6d61fc9be5eafb8a3b39d6f4c3d4a"
print("PASS: exact v10 Charon/Aeneas output receipts and hashes")
print("PASS: full-MIR default, explicit-include, and no-monomorphization LLBC receipts")
print("PASS: monomorphization duplicate-Option failure and no-monomorphization limb-loop failure are retained")
print("PASS: same-state original tail-loop success implies literal two-push success; one-way candidate helper theorem only")
print("PASS: v10 extracted outer/helper executable bodies match pinned v6 bodies")
print("Scope: candidate source/emitted-body identity only; no frozen Rust/P6 std equivalence or adoption claim.")
