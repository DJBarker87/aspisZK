# Accepted openings and causal word reconstruction

The strict C1/C2/folded leaf decoders now consume the unrestricted-byte Merkle recovery theorem directly. Accepted, recorded openings yield the corresponding lanes of the constructed literal word, without an assumed successful recovery-map entry. The recorded-run word constructor's commitment roots are derived from actual message shapes and strict record parsing.

A total table-only specification recovers the same words from the commitment first-read table. Any later first-read table can reconstruct an earlier commitment word under the same shared collision exclusion. This reuses the existing trace replay, Merkle append stability and table-representation theorems. The table representative uses classical choice; efficient extraction is not claimed. Actual accepted-source checks and concrete oracle-decoder round completion remain open.

Focused Lean 4.32.0 NUC checks only; every exit was 0, swaps were 0, and printed axioms are standard. Exact source/import pins, cap, wall time, RSS and axiom outputs are retained per target.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `RawCutConstructedWords` | 1.789 | 3634924 | 4 |
| `CanonicalCutOpeningWordProjection` | 2.122 | 3606772 | 1 |
| `RawCutTypedDecode` | 1.573 | 3587976 | 3 |
| `RawCutOpeningWordProjection` | 1.573 | 3636672 | 1 |
| `TableLogRepresentative` | 0.895 | 1810920 | 5 |
| `RawByteTableWords` | 1.562 | 3588944 | 3 |
| `RawByteLaterTableWords` | 1.548 | 3583900 | 2 |
