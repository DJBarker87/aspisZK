#!/usr/bin/env python3
"""Deterministically extract the minimal G output-0 callback source slice."""
import hashlib, json, pathlib

base = pathlib.Path("/Users/dominic/ZK/.worktrees/100bit-spend-path/docs/research/100bit-spend-path-20261013/evidence/terminal-qm31-extraction-20261016/attempt-g-name-adapt/output/generated/AspisR1SelectedMaskProbe")
types_path = base / "Types.lean"
funs_path = base / "Funs.lean"
expected = {
    "Types.lean": "0055593e96268d6451fa5750684ed54909f8652fbe9284f03b0d321834dac473",
    "Funs.lean": "8a612e11ee96c7a5a909c40bc09ef1f99e4e515b2b129f64059b5c033aa426fb",
}
assert hashlib.sha256(types_path.read_bytes()).hexdigest() == expected["Types.lean"]
assert hashlib.sha256(funs_path.read_bytes()).hexdigest() == expected["Funs.lean"]
types = types_path.read_text()
funs = funs_path.read_text()

def section(src: str, start: str, end: str) -> tuple[str, int, int]:
    a = src.index(start)
    b = src.index(end, a)
    block = src[a:b].rstrip() + "\n"
    start_line = src[:a].count("\n") + 1
    end_line = start_line + len(block.rstrip("\n").splitlines()) - 1
    return block, start_line, end_line

alias, alias_line, alias_end = section(
    types,
    "/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy_row::closure]",
    "\n\n/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#4]",
)
callback, callback_line, callback_end = section(
    funs,
    "/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy_row::{impl core::ops::function::FnMut<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy_row::closure<'_0, '_1>}::call_mut]",
    "\n\n/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy_row]:",
)
header = """-- Minimal generated G callback slice; selected generated declarations below are byte-identical to G.\nimport Aeneas.Std\nopen Aeneas Aeneas.Std Result ControlFlow Error\nset_option linter.dupNamespace false\nset_option linter.hashCommand false\nset_option linter.unusedVariables false\nset_option maxHeartbeats 1000000\nset_option maxRecDepth 2048\n\nnamespace AspisR1SelectedMaskProbe\n\n"""
footer = "\nend AspisR1SelectedMaskProbe\n"
text = header + alias + "\n" + callback + footer
assert alias in text and callback in text
assert text.count("state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut") == 3
out_path = pathlib.Path(__file__).parent / "RowCallbackSlice.lean"
out_path.write_text(text)
sha = lambda b: hashlib.sha256(b).hexdigest()
manifest = {
    "artifact": "minimal generated G row-callback slice; not compiled",
    "selected_span_bytes_verified_verbatim": True,
    "worktree": "/Users/dominic/ZK/.worktrees/100bit-spend-path",
    "extraction_attempt": "terminal-qm31-extraction-20261016/attempt-g-name-adapt",
    "source_files": {
        "Types.lean": {"path": str(types_path), "sha256": sha(types_path.read_bytes())},
        "Funs.lean": {"path": str(funs_path), "sha256": sha(funs_path.read_bytes())},
    },
    "selected_source_spans": {
        "closure_type_alias": {"source": "Types.lean", "start_line": alias_line, "end_line": alias_end, "sha256": sha(alias.encode()), "declaration": "state_only_poseidon.external_linear_lazy_row.closure"},
        "FnMut_call_mut_plus_FnOnce_and_trait_instances": {"source": "Funs.lean", "start_line": callback_line, "end_line": callback_end, "sha256": sha(callback.encode()), "declarations": ["state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut", "state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once", "state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64", "state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64"]},
    },
    "slice_file": {"path": str(out_path), "sha256": sha(text.encode())},
    "imports": ["Aeneas.Std"],
    "included_runtime_dependencies": ["Aeneas Std U32/U64/Usize", "Array.index_usize", "FromU64U32.from", "checked U64 HMul/HAdd", "Result/lift", "FnOnce/FnMut interfaces"],
    "omitted_dependencies": ["core.array.from_fn", "core.array.Array.map", "extension_from_raw_limbs", "field.M31/CM31/QM31", "parent loop", "whole Funs.lean"],
    "use_boundary": "One generated call_mut body only. It does not provide from_fn sequencing, array-map behavior, successful index facts, or full row output theorem.",
    "source_toolchain": "Rust 1.98.0-nightly commit 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65; Aeneas binary SHA 959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3",
}
(pathlib.Path(__file__).parent / "include-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
