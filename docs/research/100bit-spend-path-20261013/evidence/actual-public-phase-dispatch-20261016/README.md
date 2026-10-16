# Actual public selection through row 31

`FullPublicSelection` chooses the appropriate public-free recovery path from the absorbed round label. Its initial, semantic, opening and post-query branches are proved explicitly; correctness does not depend on an assumed failure of competing selectors.

`FullPublicEarlyCase.actual_first_cell` recovers the actual public statement for rounds 0–26 of a bounded prover experiment. `RawPublicOpeningRecovery` derives the opening walker from actual trace facts, and `FullPublicOpeningCase.canonical_first_cell` proves recovery for rounds 27–31, including the special query row. These results reuse the existing first-cell, phase and canonical-row-zero proofs. The latter case still exposes the row-zero codec premise for the total-case transport.

`RawPublicOpeningAnchor` transports actual semantic/opening table cells across an earlier query anchor into a later current table. `RawLatePublicSelector` uses the public-independent portion of the existing joint-context parser. The complete actual row-32 case is still under verification at this checkpoint. Tag 2, concrete labels, query budget and collision exclusions are explicit.

All-33 dispatch, adaptive compiled injection, source terminal acceptance and efficient extraction remain open; this is not a complete 100-bit claim.

Focused Lean 4.32.0 NUC checks; all exits 0, process swaps 0, and printed axioms standard only. Per-target receipts retain source/import pins, cap, wall time, RSS and axiom outputs.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `RawPublicOpeningRecovery` | 1.71 | 3552008 | 1 |
| `RawPublicOpeningAnchor` | 1.572 | 3546840 | 1 |
| `RawLatePublicSelector` | 1.478 | 3545648 | 1 |
| `FullPublicSelection` | 1.632 | 3552880 | 4 |
| `FullPublicEarlyCase` | 1.588 | 3548584 | 1 |
| `FullPublicOpeningCase` | 1.626 | 3551420 | 1 |
