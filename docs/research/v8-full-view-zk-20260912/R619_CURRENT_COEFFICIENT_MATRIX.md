# R618/R619 actual selected coefficient matrix

Verified boundary: the captured selected `query_arithmetic::r83_matrix` executes on every encoded QM31 input and returns exactly its four encoded coefficient rows. The captured M31 add, subtract, negate, and double operations are also proved equal to the previously verified selected operations for every raw U32 operand. This milestone does not prove the full coefficient constructor, the 38-term dot product, `combine_beta`, coherent quotient extraction, privacy, or soundness.

## Exact source and extraction

Frozen selected Rust source revision: `6677d5f1310ff7373301fbd79f186278f772e68a`, at `/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a`.

- `query_arithmetic.rs`: SHA256 `545e1dac8421bfd2bc2635590d0d6e1065a58c0f02924f25c8228f44d0a3590d`; target lines 422–427.
- `field.rs`: SHA256 `639b6425fe672e0fa6019b99b702d1f08f56cd75c4d9ad6defef854b7640f499`.
- Complete selected Rust flag argv hash: `f2485133cd857d119d387fcdda1a7fe2607e04dbec4756adbaacd3e765363613`.
- Charon binary: `b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c`.
- Generic/default-constant LLBC: `307c5518fd37ee01b90312f2b1a3f6261db809f81dfa23beaba6ef50fc4d9a01`; 214,928 bytes; `has_errors=false`. Exact narrow root and full argv are saved.
- Capture exit 0, wall 13.93 s, peak RSS 615,496 KiB, swap 0.
- Private R614D Aeneas binary: `8ce91cd041ec7bfbdc34b607abe64071e53fc11d95fa3f246058d04c73424062`. Its exact four-source-file delta, source snapshots, optimized build commands, checksums, and capped build receipt are saved. The private frontend changes do not modify Rust verifier source.
- Translation exit 0, wall 0.26 s, peak RSS 61,776 KiB, swap 0. Raw output and metadata are retained. Import-only normalization restores each raw Types/Funs file byte for byte.

The retained field NUM conversion and MAX declarations use existing pinned Aeneas definitions. No external function-behavior assumption is introduced; all eight generated-definition axiom reports contain only the standard three axioms below.

## Proved statement

For arbitrary exact base-field elements `a,b,c,d`, the actual captured matrix call on `((a,b),(c,d))`, encoded as canonical words, returns:

```text
[a,       b,       c,   d]
[-b,      a,      -d,   c]
[2c-d,    c+2d,    a,   b]
[-(c+2d), 2c-d,   -b,   a]
```

Every displayed entry is encoded in the exact M31 field. The theorem has no success, canonicality, overflow, matrix-value, or source-correspondence premise: canonicality follows from encoding arbitrary field elements. Source execution is established by the four actual operation-body identities and existing field encoding proofs. In particular, both raw fallback bodies are retained in the identities rather than deleted or assumed unreachable.

## Focused verification

Pinned Lean 4.32 cached workspace; `lake env lean -j1 -M4500`; each job uses `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`.

| Exact target | Saved run | Exit | Wall | Peak RSS KiB | Swap |
|---|---:|---:|---:|---:|---:|
| `AspisR618SelectedMatrix/Types.lean` | 1791102118993678000 | 0 | 1.05 s | 2565084 | 0 |
| `AspisR618SelectedMatrix/Funs.lean` | 1791102133599140000 | 0 | 1.16 s | 2568460 | 0 |
| `AspisR618SelectedMatrix/Axioms.lean` | 1791102169271528000 | 0 | 1.00 s | 2550828 | 0 |
| `AspisV8R19/R619MatrixArithmeticBridge.lean` | 1791102772645388000 | 0 | 1.74 s | 3749644 | 0 |

Final proof SHA256: `4f0257cca34db1285c42d4a2e2f00951baadaa9b7d308093a997c7ec2eaf1eac`. Proof build worktree revision: `96932fbf5fa6bed714933e0d70faf911f8837140`.

The five complete proof axiom reports (four operation identities and `actual_matrix_execution`) and all eight generated-definition reports contain only `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, custom behavior axiom, or opaque formatting type appears. Every focused attempt is retained with exact source, log, and receipt. The later scratch experiment adding the separate R620 algebra lemma is retained; the promoted R619 bytes are the earlier exact audited green snapshot. Promotion did not rerun any unchanged check.

## First remaining proposition

Connect the returned matrix's linear action to actual QM31 multiplication, then prove the actual constructor creates all coefficients and the actual 38-term mixed limb calculation uses them without wraparound or unchecked decoding. `core::array::from_fn` / array map and their try helpers remain constructor extraction obligations. The complete `combine_beta` translation currently has a phantom const-generic argument inference error; it is not compiled or proved by this milestone.

The whole callback chronology, universal joint C1/H1/G privacy compatibility (including p0/p2 and adaptive/degenerate prefixes), the entire published-view simulator, actual shared-oracle/seed/commitment/retry/stopping behavior and losses, coherent quotient extraction before beta, the quadratic fold, and optimized-verifier acceptance implying source-verifier acceptance remain open.

Verifier source and every security parameter are unchanged. No CU benchmark or unchanged regression was rerun. The genuine 999,790 / 999,532 CU results remain preserved. No end-to-end privacy, security, or 100-bit claim is made.
