# PCQ_B HANDOFF: phase P1b (fresh frozen extractions, probe crate)

Target not yet established. No ledger row, trust row, RSL, security contract or shipped source changed. Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 (tree d461fbc5), host workspace /home/dombarker/project-offloads/codex-pc-prov-p1b-20261109/. Tools are renamed copies of the PCO_ tools (PCQ_B_TOOLS.json: original sha256 and every textual change); the NHR stager is unchanged (PCQ_STAGER_PIN.json).

## Runs (11 extraction scopes of 30, 0 Lean scopes of 6; caps 3G/4G, swap 0, tasks 64, timeout 180 s, unraised)
All receipts: PCQ_B_ATTEMPTS.jsonl, PCQ_E4nn/receipt.json, PCQ_E4nn_emitted/PCQ_E4nn_PINS.json (tools+hashes, commands, tree/lock hashes, opaque file hash, output hashes, llbc hash). Wall 64-80 s, peak RSS about 540 MB each.
- S016 fast_pairing: E401 exit 2 (Aeneas InterpBorrows.ml:2731 in Dot::push loop); E402 ok (Dot::push opaque, root EbyKDot::push).
- S019 r1_wire: E403 Charon exit 101 (const-generic root decode_k); E409 Aeneas exit 2 (InterpReduceCollapse.ml:1880 in r1_semantic::claims). Failure list.
- S020 transport: E410 ok.
- S015 candidate query_values closure: E411 exit 2 (reaches Dot::push, same Aeneas error); E415 ok (Dot::push opaque).
- S017 multiproof Arity: E412 ok.
- S022 weights: E413 exit 2 (Nested borrows, weights.rs 229); E416 ok with raw dropped from the roots.
- S021 verifier Error/Phase: E414 ok.
- S018 NJT_claims_ref: not run, no frozen counterpart (frozen r1_semantic.rs has 318 lines, no such name).

## Coverage (PCQ_B_COVERAGE.json; presence of a same-named fresh definition, not equality)
COVERED: S015 query_values.closure; S016 EbyKDot.push; S017 Arity; S020 TAU, row_loop.body, row_loop, row, Variant (FIo_Native and Stage2); S021 Error (both), Phase (via E415); S022 Weights, scalar_factor.closure.
MISSING: Dot.push, push_loop, push_loop.body (opaque axiom); Weights.raw.closure, closure_1; all five r1_wire ValidatedRecord definitions; NJT_claims_ref.

## Gate modules ready for P2 (emission dir)
- RPz7_FIo_NativeFuns (partial: transport and EbyKDot.push only): PCQ_E410_emitted/raw/PCQ_aspis_r1_cost_probe_transport, PCQ_E402_emitted/raw/PCQ_aspis_r1_cost_probe_fast_pairing.
- RPz7_FIo_NativeTypes (partial: transport.Variant, verifier.Error, weights.Weights): E410, E414 (.../PCQ_aspis_r1_cost_probe_verifier), E416 (.../PCQ_aspis_r1_cost_probe_weights).
- Stage2ContinuationTypes (partial: candidate closure, multiproof.Arity, transport.Variant, verifier.Error/Phase): E415 (.../PCQ_aspis_r1_cost_probe_candidate), E412 (.../PCQ_aspis_r1_cost_probe_multiproof), E410, E414.
Not ready: AspisR1DecodeKFullV10.Funs, NJT_ClaimsRef_Funs (failure list).

## Hand models (PCQ_B_HAND_MODELS.json, record only)
No non-Aeneas-generated gate file in the checked import closure defines a name the P1b fresh runs emit or leave external. Gate-side Aeneas-generated bodies vs fresh opaque externals (WideExact, WideExact.to_limbs, Dot.push, COEFFICIENT_TO_ROW) are listed separately, together with the hand-written gate files in each closure. The search resolves imports by name else unique basename over the research tree (script PCQ_B_coverage.py); a name defined only outside that closure would be missed.

## Remaining / not established
No equality proved. Aeneas version b59d5188 cannot translate Dot::push, Weights::raw closures, or the claims/decode_k chain; those need either a source-side restructure (not allowed here) or an accepted P3 obligation. The gate RPz7 sources have no recorded extraction configuration; the fresh runs here are new, not reproductions. Toolchain label mismatch noted in PCQ_B_CLASSIFICATIONS.json B-7.
