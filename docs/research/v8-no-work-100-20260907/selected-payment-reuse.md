# Selected payment amounts: reuse of the V7 field proof

Research continuation from `f021007879dcd9e2bca795b4758e187fa1c3b302`.
No verifier, protocol, production source, parameter or wire change.

## Deterministic endpoint

The new [SelectedPaymentRecovery.lean](experiments/SelectedPaymentRecovery.lean)
ports the **existing range and field-to-natural proofs**, rather than copying
the old accepted-path conclusion. It maps the selected pair-forest direct
30-bit layout into `ArithmetizationCore.RangeWitness`, derives its residuals,
and invokes `range_value_sound` and `nat_of_field_eq`.

The endpoint is deliberately below full witness validity:

```
canonical recovered source cells
 + exact selected individual bit/recomposition/copy residuals
 + exact two conservation residuals
 -> actual raw decoder amounts < 2^30
    AND input = recipient + change over natural numbers
    AND the output sum cannot overflow u32.
```

No decoder-success, honest-compilation, original-witness equality, family
membership, inactive-exactness or accepted-proof hypothesis is used.
Individual residual satisfaction is an **upstream obligation**, not a
consequence of acceptance proved here. This leaf adds no probability term.
`ValueResiduals` is a **sufficient subset**, not the complete inventory of
the selected compiled range lanes. It does not redefine what the verifier
accepts or license removing the remaining equations.

The direct 30-cell weighted sum is symbolically partitioned into three
10-bit limbs. Those limbs are mathematical intermediate sums, **not extra
committed columns or proof messages**. Canonical representatives connect the
field theorem to the raw `M31.0` values read by `recovered_witness::decode`.

## Exact selected source map

The table is `table(row, column) = c1[column][row]`. Only the first 16
semantic columns of the 26-column commitment are relevant to this leaf.

| Obligation | Selected cells / source |
|---|---|
| Decoder values | `(44,0)`, `(460,0)`, `(508,0)` in [recovered_witness.rs](experiments/recovered_witness.rs) |
| Range rows | `1008+2*v`, its successor, and XOR12 row; columns `0..9` |
| Range recomposition | column 10 of `1008`, `1010`, `1012` |
| Third bit rows | `1020`, `1022`, `1016`, respectively |
| ValueSource copies | `(44,0)->(1008,10)`, `(460,0)->(1010,10)`, `(508,0)->(1012,10)` |
| Conservation copies | `(1008,10)->(1014,0)`, `(1010,10)->(1014,1)`, `(1012,10)->(1015,1)`, `(1014,2)->(1015,0)` |
| Host/theorem conservation orientation | `t[1014,2]-(t[1014,0]-t[1014,1])`; `t[1015,0]-t[1015,1]` |
| Public assets | `(44,1)`, `(460,1)`, `(508,1)` each equal the independent public asset |

The Rust source of this map is `pair_tree_hiding.rs:155`,
`pair_trace.rs:1103`, `pair_forest_trace.rs:412`, and the direct value
evaluator `pair_constraint_residuals.rs:457`. Forest residual assembly
projects its last 16 rows to legacy `960..975`, and retains the legacy
bit/recomposition/conservation expressions. The transfer-only recipient
copy has weight one for this transfer slice; withdrawal is not inferred.
The source-map inspection is **not a generated Rust-to-Lean translation**.

Two compiled-source details matter at that boundary:

- `pair_forest_semantic_terminal.rs:501` also places `succ_z[10]` and
  `xor12_z[10]` in the range lanes. At the three selected value rows these
  are the six equations requiring column 10 at rows
  `1009,1011,1013,1020,1022,1016` to vanish. They are **distinct from the
  3,803 relation-free host-padding cells**. The new sufficient-subset
  theorem does not need these six premises; the compiled verifier still
  enforces them. No full compiled-range-inventory equality is claimed.
- The first compiled conservation lane at
  `pair_forest_semantic_terminal.rs:515` uses `z[0]-z[1]-z[2]`, the negative
  of the host/theorem expression `z[2]-(z[0]-z[1])`. Their **zero predicates
  are equivalent**, not their literal polynomial expressions. The second
  conservation expression has the same orientation. Likewise the compiled
  Boolean expression `b²-b` equals the theorem's `b*(b-1)` algebraically.
  Transferring scalar packed acceptance to the individual equations still
  requires the selector/batching and source correspondence obligations;
  this leaf does not bypass them.

The masked acceptance predicate does not use the host evaluator's 3,803
zero-padding residuals. This leaf imposes none of that padding class. Every listed auxiliary
coordinate is relation-used, and the decoder's sponge source rows have
local offset 12. Existing `PaymentMaskRead` already proves the raw decoder
footprint invariant under allowed mask additions; that completed proof is
not replayed. We do not conclude that masks preserve the full adaptive view.

## What can and cannot be reused

| V7 result | Reuse status |
|---|---|
| `ArithmetizationCore.range_value_sound` | **Directly reused** after deriving its virtual-limb interface from the selected 30-bit residuals |
| `ArithmetizationCore.nat_of_field_eq` | **Directly reused** for two private output amounts with independently derived bounds |
| `V7DeterministicSpendWitness` | Its separation of deterministic decoding from probabilistic coverage is retained; its older `OpenedColumns` endpoint is not applied |
| `NativePaymentTerminalBridgeV1` | Not applied: its native source rows `44/444/492`, range start 864, and 20-level geometry do not describe this selected forest |
| `V7CoherentTraceExtraction` | Not applied to V8: its same-support/decoder membership and raw-word one-fold obligations are different |
| `V7RestoredSemanticWitness` | Not applied: its point-exactness, family membership, `inactiveExact`, and source/execution hypotheses remain essential to its actual theorem |

The inherited arithmetic files were last changed at
`2b2a2438c7c6a2038fcbcd46cf075e61e0af5e0b`. Their checked cache sources
match this research commit byte-for-byte. This leaf does **not** import the
old cryptographic capstone or promote its conditional hypotheses.

## Boundary regression: positivity is separate

`zero_amount_slice_satisfies_residuals` preserves a useful exact limitation:
an all-zero amount slice satisfies these bit, recomposition and conservation
residuals, so this slice cannot prove strict positivity. The selected pair
trace compiler checks input positivity at `pair_trace.rs:501`, and both
private output amounts at `pair_trace.rs:621`.

This is **not** a full semantic trace, a proof-acceptance result, or a payment
forgery. Other hash/path/public constraints have not been supplied. It means
that a complete theorem ending specifically at the current compiler-backed
`extract_checked` must derive the additional positive-amount requirements
from actual earlier premises, or explicitly distinguish the accepted
payment predicate from that compiler's stronger fixture admission rules.
It cannot silently assume them from 30-bit range checks. No check was changed.

## Remaining path and next obligation

| Stage | Status after this leaf |
|---|---|
| Authenticated C1 access / coefficient recovery | Existing byte-preserving SHA query-graph extractor and totalized Gao same-execution fixtures, plus mathematical finite-fuel Gao completeness; actual adversary/replay coupling and source refinement remain separate |
| Raw canonical source amounts -> bounds and integer conservation | New kernel-checked target, with exact individual residual hypotheses |
| Owner secret, salts, note/nullifier commitments | Decoder reads known; universal source-shaped Poseidon/copy-to-hash bridge remains |
| Occupancy and 24-level lane/forest membership | Existing one-step path lemma and executable validator; full universal chain remains |
| Runtime, spent nullifier and exact settlement | Caller/validator obligations; not replaced with prover-produced context |
| Acceptance -> all required residuals / positive values / witness success | Open; early C1 fixing, semantic/copy collision classification and source connection still required |

The useful next deterministic experiment is a selected **sponge absorption
and copy-chain bridge** for owner/input-note/nullifier rows: derive the
decoded digest inputs from individual round/schedule/copy residuals and
reuse the existing Poseidon model without assuming those final hash
equations. In parallel the global accepted-unrecovered event must continue
to charge missing access, decoder failures and actual provider-none paths.

The [query-graph](query-graph-review.md), [raw-C1](raw-c1-review.md) and
[Gao](gao-recovery-review.md) milestones supersede the early extra-opening
fixture. They include genuine accepted non-polynomial/noncanonical C1
executions with checked witnesses recovered from the same frozen C1 hash
graph. This new amount proof consumes that intended recovered coefficient
endpoint; it does not revert to an extra-opening-only access contract.
The raw graph remains an instrumented ROM-style model rather than a coupled
actual-adversary extractor. The proved Gao algorithm is a mathematical
polynomial model, not yet an extracted Rust implementation/runtime theorem.

Wire remains `697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282` bytes.
No new CU, proving, privacy or Fiat-Shamir measurement is claimed.

## Reproduction and formal evidence

Run only the changed leaf with the guarded cached runner:

```
bash docs/research/v8-no-work-100-20260907/experiments/run_selected_payment_recovery.sh \
  /absolute/new-evidence-log
```

The runner pins committed source hashes, cached oleans, Mathlib revision
`81a5d257c8e410db227a6665ed08f64fea08e997`, and records the source revision,
Lean version, target hashes, exit, wall time, peak RSS, swap and axiom audit.
It uses `lake env lean -M7000` and does not build dependencies.

Final [v3 evidence](experiments/selected-payment-lean-v3.log): **exit 0,
6.45 s wall, 5,576,818,688 bytes peak RSS, zero swaps**. Nine public theorem
audits contain only `propext`, `Classical.choice`, `Quot.sound` (some use a
subset). No new axiom or retained incomplete proof. Source SHA256:
`4c8ba95e27ed5e50e1927b6e9233b9f387b8674f5ca059949f8cd04ca7a63c18`;
olean `ee2166caaf0ff244add6113c14b19fd8622c00fbd87607b195063b42323e3ac0`.
The run was exclusive of other agents' Lean jobs; cached imports were not
rebuilt, and the research/main worktrees were not switched or reset.

Two local preflights are retained, not counted as proof successes:

- [v1](experiments/selected-payment-lean-v1.log): exit 1, 29.51 s,
  5,504,319,488 bytes RSS, zero swaps. A concrete-field `congr` in the
  30-term partition hit the default heartbeat limit; explicit modulus
  unfolding and one small source-row normalization were also missing.
  The partition was generalized to `AddCommMonoid K` before field
  instantiation, rather than raising limits or replaying unchanged.
- [v2](experiments/selected-payment-lean-v2.log): exit 1, 9.34 s,
  5,510,905,856 bytes RSS, zero swaps. The symbolic partition solved the
  goal earlier, leaving an extra tactic bullet. Removing that dead bullet
  produced the clean v3 audit. Failure-generated `sorryAx` in the first
  log is not present in the retained v3 declarations.
