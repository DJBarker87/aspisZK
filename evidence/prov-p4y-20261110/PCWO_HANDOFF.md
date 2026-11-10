# PCWO_ handoff (phase P4y, third tool version). Target not yet established.

Tool: fork of Aeneas 0d21a9ec + patches A (PrePasses.update_loops: continuation of the enclosing statements used when the loop block is exhausted) and B (SymbolicToPureTypes.translate_fun_sigs: keep trait_type_constraints instead of asserting empty), Charon 454586e9 reused. Diffs and sha256 in PCWO_PATCHES/, build receipt PCWO_TOOL_BUILD.json (PCWO_T001 exit 0, 802 s, patched binary sha256 6652776a...d28b, image pcwo-aeneas-pair:t001 kept for a rebuild).

Results (nothing credited, no fresh = gate statement exists):
- op50: patch A passes the early-return pre-pass; Aeneas now fails later with "Could not match the contexts" (r1_pool_adapter.rs 495-520). PCWO_E001.
- semantic_boundary/claims/semantic_rounds: patch B passes the CFailure; new errors are "Arrow types" (semantic_boundary) and shared-loan join (claims; semantic_rounds depends). PCWO_E002.
See PCWO_CANNOT_EXTRACT.json. Budget used: tool-build 1/2, extraction 2/6, Lean 0/10. Placeholder emissions not committed (hashes in raw.sha256).

Target not yet established
