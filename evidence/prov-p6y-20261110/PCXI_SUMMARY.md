# PCXI_ summary: re-derivation of the 183 RECEIPTED cone definitions without pin-equal evidence

Provenance only; no ledger row, trust row, RSL, contract or shipped source changed; no Lean, extraction or Kani scope was run (budget unused). Frozen source 4bb3b3f. Target not yet established.

## Counts

| verdict | definitions |
|---|---|
| PIN_EQUAL | 64 |
| TEXT_DIFFERS | 79 |
| NOT_REDERIVABLE | 40 |

Subtypes: NOT_REDERIVABLE/CONFIG_NOT_PINNED 4; NOT_REDERIVABLE/- 36; PIN_EQUAL/- 64; TEXT_DIFFERS/DEPENDENCY_CONTEXT_DIFFERS 4; TEXT_DIFFERS/EMISSION_DIFFERS_FROM_FRESH_FROZEN 8; TEXT_DIFFERS/NO_FROZEN_COUNTERPART 34; TEXT_DIFFERS/TEXT 33

## Split of the 1707 cone definitions

| class | before (PCXG_) | after |
|---|---|---|
| SETTLED | 993 | 1057 |
| NOT SETTLED | 649 | 585 |

NOT SETTLED after = OPEN 466 + TEXT_DIFFERS 79 + NOT_REDERIVABLE 40. Listed separately and unchanged: 65 (EQUALITY_DOMAIN 6, CONDITIONAL_ON_BINDING 43, DEPENDS_ON_LIBRARY_TRUST 7, HAND_ADAPTED 5, NO_FROZEN_COUNTERPART 4). 1057 + 585 + 65 = 1707.

## What PIN_EQUAL means here

The Rust text of the item in the receipted extraction input equals the 4bb3b3f text (normalised), its local callees and local types/consts equal their frozen counterparts, and the extraction either has no overflow-sensitive operator or ran with CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true. It does not prove that the gate Lean definition is that emission: the link from gate module to emitted file is the candidate sha256 of PCO_PARTITION (hash identity), unchanged. For definitions with PCO coverage COVERED_DIFFERS the Rust text can be equal while the receipted Lean differs from a fresh frozen emission; those are TEXT_DIFFERS (EMISSION_DIFFERS_FROM_FRESH_FROZEN), not credited. Dependency context of probe/cut crates was checked for local functions, types and consts only; external crate items were not compared.

## By module

| module | PIN_EQUAL | TEXT_DIFFERS | NOT_REDERIVABLE |
|---|---|---|---|
| AspisR1Qm31ArithmeticProbe.Funs | 6 | 7 | 0 |
| AspisR1Qm31ArithmeticProbe.Types | 3 | 0 | 0 |
| AspisR1RowShape.Funs | 4 | 0 | 0 |
| AspisR1WithdrawalValidation.Funs | 8 | 0 | 0 |
| NCO_Reference.Funs | 0 | 0 | 1 |
| NCV_Reference.Funs | 0 | 29 | 0 |
| NCV_Reference.Types | 0 | 1 | 0 |
| NCX_Reference.Funs | 6 | 16 | 0 |
| NCX_Reference.Types | 2 | 2 | 0 |
| NDH_TranscriptReference.Funs | 0 | 0 | 3 |
| NDI_BatchRef.Funs | 0 | 5 | 0 |
| NEA_Reference.Funs | 0 | 0 | 1 |
| NEG_PushActual.Funs | 0 | 8 | 0 |
| NEG_RowIsolated.Types | 0 | 0 | 3 |
| NEI_FourWrapper.Funs | 1 | 0 | 0 |
| NEI_LineFull.Funs | 0 | 0 | 1 |
| NEI_LineFull.Types | 0 | 0 | 1 |
| NEV_CodeFieldRaw.Types | 3 | 0 | 0 |
| NFQ_Reference.Funs | 0 | 1 | 0 |
| NFQ_ScanReference.Funs | 0 | 1 | 0 |
| NGD_AtG.Funs | 0 | 1 | 0 |
| NGD_SlotRef.Funs | 1 | 4 | 0 |
| NGW_HelperRef.Funs | 0 | 3 | 0 |
| NKV_FRef | 0 | 0 | 3 |
| Op3I_Source | 24 | 1 | 3 |
| Op4P_Extract.Funs | 0 | 0 | 9 |
| Port1_LibrarySource | 0 | 0 | 1 |
| Port3_NativePendingBody | 0 | 0 | 2 |
| Port3_NativeQueryBody | 6 | 0 | 4 |
| Port4C_NativePrefix | 0 | 0 | 3 |
| SAQ_InverseExplicitMul | 0 | 0 | 4 |
| SAQ_InverseTypes | 0 | 0 | 1 |

Per-definition evidence (receipt files, revision, tree-dirty flag, overflow configuration, item hashes, first difference) is in PCXI_RECEIPTS.json.

Target not yet established.
