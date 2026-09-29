# R83: unchanged-proof opening and ordinary contractions

2026-09-29. Control: R82 `d137f7316e0878bfb90780c13214a7586287deb2`.

The selected complete verifier uses **1,326,977 / 1,328,177 CU**, saving
6,835 / 6,824 against R82 on the same two frozen proofs. Both actual 1M
honest executions still exhaust; the larger fixture is **328,177 CU** over.
No protocol, wire, mask, basis, query count or acceptance check changed.

| Experiment | World 0 CU | World 1 CU | Decision |
|---|---:|---:|---|
| R82 control | 1,333,812 | 1,335,001 | Retained control |
| Complementary tensor reconstruction | 1,335,325 | 1,336,521 | Reject regression |
| Short-dot ordinary block contraction | 1,331,290 | 1,332,484 | Compose |
| Mixed-width packed opening contraction | 1,329,509 | 1,330,704 | Compose |
| **Opening + block** | **1,326,977** | **1,328,177** | **Selected** |

The opening calculation prepares the four base-field matrix columns for
each of the three helper multipliers once. Each decoded slot then uses four
38-term M31 dots (26 C1 scalars and 12 helper limbs). Nine four-product chunks
and a two-product tail share the final reductions. For canonical inputs,
four products fit in u64; each partial fold is below 5P and their total is
below 50P. These are inspected integer bounds, not new Lean theorems.
The actual decoder still checks every one of the 152 limbs, including zero
batching coefficients; authentication uses the original unchanged bytes.

The ordinary block rewrite reuses the existing short-dot kernels and removes
the first round's multiplication by one/addition of zero. It retains all
powers, carry terms, final coefficients and eight halvings. The original
block implementation remains the differential oracle. The tensor candidate
reduced products but increased complete CU, so it was not selected.

All four measured candidates passed the focused source tests, the retained
ordinary/G and semantic-basis comparisons, all 3,281 wire cases, stack-safe
SBF builds and complete honest/malformed runtime checks. The packed gate
adds 4,096 arbitrary coefficient profiles including all 152 input basis
positions and maximal canonical limbs. The selected build's ELF hash is
`cb61f4e17f855ef23405876de36a31d7a9280b9304ae472ab27f51ca7457f21b`.

An opt-level-2 experiment failed the stack gate: reported frames were 4,288,
4,416 and 6,208 bytes. The compiler itself exited zero but the runner rejected
the diagnostics; that ELF was never simulated. Its dedicated saved limits
receipt is missing, so no such receipt is fabricated. The runner checked
limits on entry. The first packed draft had a missing parenthesis and never
compiled; its failed stage is preserved separately from the corrected stage.

Evidence: `tools/check_r83_evidence.py` verifies 136 public artifacts, exact
source deltas, timings/RSS/zero swaps, successful-stage live cgroup receipts,
unchanged proofs/driver/heap and the actual 1M failures. Selected source has
211 pins, including the previously unpinned separate SBF Cargo profile.
Earlier completed stages retain their original 210-pin manifests.

NUC jobs used zero-swap caps: host 5/7 GiB, SBF 12/16 GiB, simulation 2/3 GiB
high/max, TasksMax=128. Selected SBF build: exit 0, 25.19 s, 601,428 KiB peak
process RSS. Full measurements are in the evidence receipt.

The Solana skill's source-test, stack and complete-execution gates were used.
No new Lean work, deployment, wallet operation, privacy assumption or security
parameter reduction. Existing full privacy/soundness obligations remain open.
R84's new-profile bit-permutation screening is separate from this result.
