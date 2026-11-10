# PCWM_ HANDOFF: phase P5c-2 (P5d), OPEN definitions, third module batch

Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; Pool b936275. Branch codex/pc-prov-p5d-20261110. No ledger row, trust row, RSL, security contract or shipped source changed; nothing pushed or merged. Lean scopes 23 of 35 (L020-L023 recompiled the four files at the default 200000 heartbeat limit after the lead hygiene fix, all exit 0), extraction 6 of 10, one at a time, caps unraised, swap 0, peak RSS about 2.6 GiB (Lean) and 0.75 GiB (extraction). Cargo --jobs 4 and CARGO_BUILD_JOBS=4, rustc -Zthreads 1; identity by class receipt PCWE_E003.

## Difference at a matching configuration
None found. Every equality that was attempted at ON compiled, with encoding differences only (name flattening, external constants as Result axioms, the local CodecError carrier of the reconstructed S1 crate).

## Per module (62 OPEN keys; lead correction: conditional items and the reconstructed module are not SETTLED)
* AspisR1PublicPreparation.Types: 8 of 8 SETTLED (PRVEq_..._Types_w1..w4, L005 to L008). Equivalences against four ON frozen Types texts.
* NEV_AccumulateRaw.Types: 7 of 7 SETTLED (PRVEq_NEV_AccumulateRaw_Types_w1, L004), fresh text PCVJ_E002 (extended Aeneas).
* AspisR1WithdrawalCaller.Funs: 8 of 8 SETTLED, 3 of them CONDITIONAL_ON_BINDING (encode_digest_canonical and its loop and body: same HM-B/HM-D externals, aspis-core to_le_bytes bound to the new frozen emission PCWM_E001); L012.
* AspisR1Qm31SamplerIndex.Funs: 7 of 7 SETTLED_CONDITIONAL_ON_BINDING (aspis_core field P, and CM31.new for qm31_sample), L002; fresh text PCQK_E015.
* S1ValuesOwnedModelV1: 8 of 8 SETTLED as ReconstructedSource, not frozen-equal (PCWC_E001 emission; values_owned_reference with the error carrier mapped), L019.
* AspisR1SemanticCallExtraction.Funs: 8 OPEN. semantic_boundary and semantic_value CANNOT_EXTRACT (original Aeneas: Internal error at core iter traits iterator.rs 42:0-42:24; extended: Arrow types are not supported yet at r1_semantic.rs 82:0-85:1, E004 to E006). The loop, body and entry definitions are gate-side helpers with no frozen counterpart.
* S8OwnedP6.Funs: 8 OPEN, NO_FROZEN_COUNTERPART (tools crate only).
* OraclePortCkptAbi2Extracted.Funs: 8 OPEN, NO_FROZEN_COUNTERPART and WRONG_BASIS (tools crate only; not extracted again).
Total of the 62 definitions: 30 SETTLED against frozen emissions (20 unconditional and 10 CONDITIONAL_ON_BINDING: 3 in WithdrawalCaller and 7 in Qm31), 8 SETTLED as ReconstructedSource, 24 OPEN. Exact per-module counts: PCWM_STATUS.json.

## What this is not
No row table entry is credited by this handoff; the lead recounts. The conditional items carry their binding in the statement shape (shim definitions) and in PCWM_CLASSIFICATIONS.json. Equivalences of types are isomorphisms, not equality of the Lean types.

## Not closed and next deliverable
semantic_boundary and semantic_value need an Aeneas route for Iterator::fold with fn-item and closure arguments (PCWH lane) or an opaque cut with an HM-B model row; S8OwnedP6 and OraclePort have no counterpart in the pin, so they stay OPEN unless the owner names a source for them.

Target not yet established.
