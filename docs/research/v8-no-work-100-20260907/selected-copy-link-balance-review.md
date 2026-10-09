# Selected weighted rows to the literal active-link balance

Continuation from `f0f46ffede8812252ac7cee9edf5547f228533d5` on the existing
research branch. The previous two layout leaves are consumed unchanged.
No Rust, main-branch, protocol, transcript, proof-body or verifier-operation
change was made.

## New deterministic result

`SelectedCopyLinkBalance.lean` proves that the constructed selected row
family has exactly the rational contribution of the actual 136 links:

```
sum_row rationalContribution(sourceRows[row], chi)
  = sum_link weight[link] *
      (1/(chi - compressed_producer[link])
       - 1/(chi - compressed_consumer[link]))
  = sum_{publicly active links}
      (1/(chi - compressed_producer[link])
       - 1/(chi - compressed_consumer[link])).
```

The endpoint `source_active_links_zero` then consumes the already-proved
constructed-row theorem. Its prerequisites remain:

- Every selected Boolean copy-row residual is zero.
- The total helper sum is zero.
- The inactive helper sum is zero.
- All four slot denominators are nonzero on every active row, **including
  zero-weight or empty slots**.

Under those prerequisites the actual selected active-link rational balance
is zero. The result does not assume an inactive-weight condition, slot
uniqueness, valid witness, decoder success, honest trace, or an implication
from verifier acceptance. The first two static properties are now derived
from the literal layout; the other assumptions are deliberately not used.

## Source data and the weighted port

The definitions reuse `SelectedCopyLayoutRows.sourceRows`, hence the exact
136 endpoint pairs, all 14 tuple patterns and their offsets, and the selected
five-kind public weight schedule. In particular, pattern 10's final-limb
offset `1051521018` remains present. Tags are the selected sequence starting
at `1124073472`. No 183-link or 78/75-link registry is substituted.

The relevant pinned source files and SHA-256 hashes are:

| Source | SHA-256 |
|---|---|
| `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs` | `cfce7ec499d3cfd54cf91eb88675e45d89ada5ce073fe00c78be5211204fbc50` |
| `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs` | `50062fff8b6afbffad3ddbb8eda09992353a9171c4955151cece26a654c6a6d5` |
| `AspisFormal/AspisFormal/Pool/NativePaymentCompiledCopyLogUpV1.lean` | `86b10589ca637514f0eb772a0bb29e9da28304c50f7aa1627bccf2ddbed1993f` |

The existing Native proof supplies the useful mathematical pattern:
`nativeSlotValue_eq_of_placed`, `native_slot_rational_eq_link_sum`, and
`native_sum_slot_rational_eq_link_sum`. Its slot weight is one for an
occupied slot, whereas the selected model sums the actual public weights.
The new proof ports the argument with arbitrary per-link weights; it does
not import the Native leaf's uncached endpoint closure or assume its
unweighted instantiation applies.

Both producer and consumer placements are separately injective. They may
share a position across sides, which is harmless. A source endpoint's key
is `2*row + slot`. Two explicit lookup lists provide a checked left inverse
for every literal endpoint. The finite certificates check 136 entries per
side; the subsequent injectivity and all field reasoning are symbolic.
The lookup lists are not a new trusted registry: the kernel checks each
one against the imported literal `sourceLinks` function.

At an occupied slot, the gathered value is exactly its link's compressed
tuple and the gathered weight is exactly its public weight. At an empty
slot both gathers are zero. Finite-sum exchange then gives the whole-table
identity. Crucially, the value gather never multiplies the tuple by its
weight. A zero-weight link can still create a denominator pole in the
cross-multiplied source residual.

The row-to-link identity itself holds even at poles because field inverse
is total. This does **not** eliminate the non-pole prerequisites of the
local-residual-to-helper theorem. `source_active_links_zero` retains them
in full. The previous zero-weight-pole regression remains applicable.

## Status and next deterministic endpoint

| Interface | Status |
|---|---|
| Literal producer/consumer placement uniqueness | Newly kernel-checked |
| Occupied and empty weighted slot behavior | Newly kernel-checked |
| Constructed whole-row rational sum equals literal weighted link sum | Newly kernel-checked |
| Public zero/one weights select the actual active-link sum | Newly kernel-checked |
| Local residuals and both helper boundaries imply that sum is zero | Newly composed, with all four slot poles retained |
| Optimized Rust selector/pattern/accumulation loop equals this field model | Still a source-refinement obligation; metadata equality is not machine translation |
| Zero rational balance outside chi collisions implies equal active compressed multisets | Not proved in this continuation |
| Excluding lambda compression collisions yields all selected weighted tuple aliases | Not proved in this continuation |
| Acceptance enforces local residuals and both helper boundaries | Still a causal semantic/relation-source obligation |

The next bounded step is the weighted version of the Native collision-explicit
alias argument: use tagged and compressed multisets **restricted to the
selected public active-link set**, then use the injective natural tags to
identify each matching link. Its correct output is
`weight*(producer_limb-consumer_limb)=0`, not equality on inactive links.
The current selected source has 136 links and 16 limbs per tuple; an old
registry's error numerator cannot be imported mechanically.

A concrete consumer is the seven singleton transfer links at indices
11 through 17, already modeled in `SelectedAmountEndpoint`. They connect
the note amount cells `(44,0)`, `(460,0)`, `(508,0)` through the exact helper
cells to rows 1014/1015. Closing their aliases from the global copy relation
would discharge a real premise of that amount endpoint, not redefine
validator success. This continuation stops at the checked link balance
rather than presenting collision exclusions as achieved probability bounds.

The candidate C1 table must still be fixed at the appropriate pre-lambda
family boundary. Public variant/append index require their authentic source
binding, while the helper may depend on earlier challenges. These are
causality/source obligations, not consequences of a deterministic sum
identity. No new extraction, soundness or Fiat–Shamir probability is claimed.

## Focused evidence

Only the new leaf was checked, in the prepared NUC scope
`/home/dombarker/project-offloads/aspis-symbolic-ood.zZbNpg`, using
`run_symbolic_ood_nuc.sh`. No previous green leaf, package or full manifest
was replayed and no dependency was built cold. The recorded borrowed-source
pin is `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`; native package artifacts
remain the explicitly pinned-revision cache boundary, not a fresh replay.

| Attempt | Result | Wall time | Peak RSS | Swap |
|---|---|---:|---:|---:|
| `selected-copy-link-balance-nuc-v1` | Exit 1: static all-pairs recursion limit and one local rewrite | 0.94 s | 1,729,116 KiB | 0 |
| `selected-copy-link-balance-nuc-v2` | Exit 0; all 12 printed audits standard-only | 6.02 s | 1,995,332 KiB | 0 |

The first attempt's naive all-pairs injectivity computation hit the fixed
recursion limit of 1000; it did not hit memory pressure. The replacement
proves a left inverse with one certificate entry per endpoint, then derives
injectivity symbolically. The empty-slot rewrite was also made explicit.
No recursion, heartbeat, heap, cgroup or time limit was raised. The complete
failed source snapshot, log and per-run manifest are retained; its diagnostic
`sorryAx` entries are not claimed results. The final source has no `sorry`
or new axioms. Its four static audits use only `propext`; the remaining
eight use only standard axioms.

The command for the green check was:

```sh
ssh -o BatchMode=yes dombarker@nuc.local 'bash /home/dombarker/project-offloads/aspis-symbolic-ood.zZbNpg/run_symbolic_ood_nuc.sh /home/dombarker/project-offloads/aspis-symbolic-ood.zZbNpg SelectedCopyLinkBalance selected-copy-link-balance-nuc-v2'
```

The runner records Lean 4.32.0, `-j1 -M9500`, `MemoryHigh=8 GiB`,
`MemoryMax=10 GiB`, `MemorySwapMax=0`, and `CPUQuota=200%`, plus the exact
source/output/runner/manifest hashes and before/after overlay checks.

| Artifact | SHA-256 |
|---|---|
| Final `SelectedCopyLinkBalance.lean` | `78235569a8cf7ad34f2e9d2e3907bfc17b26b19b0016df7ab86c78620024b06c` |
| Green `.olean` | `897b1b0df7f5f0102d5877a264dda5ac17b1bcf8e4b34580df5c540aa0d91ab7` |
| v1 failed source snapshot | `8a21376d89a4e70b278fcf3fc653d4b35b93d96f6444ab70b04930d3065cac9d` |
| v1 log | `7a56771bdcbd847e924926b0be98e3473214273fb685c081dc5aca847923d0ab` |
| v1 manifest | `8e7f3bee12e1588d04538e83f7d28bbff1eaad58f2bc9506531a4eda5506b517` |
| v2 log | `ae13f2b7fcb82b940dced7925b6dc88fcca320c2c026d4fc6995e30d3db3514a` |
| v2 manifest | `5c5761ea9f69debaec60d8091485803b169de296e080b86dcbaa88a17c7393b8` |

The v2 source snapshot matches the final source. All artifacts above are
retained under `experiments/`; the `.olean` is a local cache artifact.

There was a brief scheduling exception, not concealed as serial timing.
The journal records root's capped `CurveOODDerivative` v1 starting at
23:48:39 UTC and finishing at 23:48:42, while this capped v2 check ran from
23:48:40 to 23:48:46 on 2026-09-09. The overlapping grant/hold messages
therefore caused approximately two seconds of overlap, at one-second
journal precision. The excerpt and command are retained in
`experiments/selected-copy-link-balance-scope-timing.log` (SHA-256
`31848c42b2e629d4adbe114df09ad693efc6fba1c51f47c04ff65537ea590c11`).
No aggregate peak RSS was measured. Individual caps remained in force,
both jobs completed, and this timing is not presented as a serialized
performance comparison. The source/olean provenance checks still passed.

The body allowance remains 40,282 bytes. No proof generation, SBF, full
transaction CU, privacy, witness-extraction runtime or deployment gate was
run. The scoped Lean source is frozen; no commit or push was made by the
subagent.
