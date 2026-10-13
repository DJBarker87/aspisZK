# Bounded values and output-note extraction

This checkpoint strengthens the R1 field-model extraction from an input note
to bounded integer conservation and recipient/change note bindings. It reuses
the existing value-row, copy-balance, Poseidon, schedule, asset, digest, and
input-note theorems. No historical Lean statement or production constraint was
changed. It is not yet a full spend, append-transition, source-refinement,
Fiat–Shamir, or zero-knowledge theorem.

## Exact new conclusions

`SpendValues.of_value_balance` takes `Holds valueFamily`, `CopyLinkBalance`,
and characteristic `2^31-1`. It produces natural values `v0`, `v1`, and `v2`,
each below `2^30`, represented by the trace's three value cells at rows 1008,
1010, and 1012. It proves `v0 = v1 + v2` as an integer equality. The existing
`valueRow_nat` proves the bounds; `positivity_copy_cells` connects the amount
cells to the conservation gates. Both sides of the resulting cast equality
are strictly below the characteristic, so the existing modular-equality
theorem gives integer equality without wraparound.

This theorem does **not** assume `Holds positiveFamily`. That family is
absent from `ProductionHolds`; the old `positivity_of_balance` theorem needs
it for its stronger strict-positivity conclusion. The new proof uses the
production facts needed for bounds and conservation, and makes no claim that
the recipient or change value must be positive.

`OutputCopyLinks` projects six named entries of the literal copy registry:

| Note | Links in `copyLinksBeforePositivity` | Constraint |
|---|---|---|
| Change | 5, 6 | Full-state continuations from blocks 30 to 31 to 32 |
| Change | 13 | Middle-chunk value at `(0,508)` equals bounded value `(10,1012)` |
| Recipient | 3, 4 | Full-state continuations from blocks 27 to 28 to 29 |
| Recipient | 12 | Middle-chunk value at `(0,460)` equals bounded value `(10,1010)` |

Change links have weight kind 0 and are always enabled. Recipient links have
weight kind 1 and the theorem explicitly requires `privateTransfer`.

`OutputNotes` follows the existing input-note proof's symbolic three-block
composition. The first chunk supplies the output public key; the middle
chunk supplies value, asset, and six salt limbs; the final chunk supplies
two salt limbs and six proved zero padding limbs. Schedule gates set the
note domain and length; asset gates give the public asset; the existing
Poseidon theorem proves each block step without evaluating the permutation.
The digest family then binds the final outputs to the public commitments:

- Change is proved for both variants, using blocks 30/31/32 and output row 523.
- Recipient is proved for `privateTransfer` using blocks 27/28/29 and row 475,
  additionally requiring `pub.recipient = some recipient` for public binding.

The extracted output keys are arbitrary public-key preimages of those notes.
No secret-key ownership of either output key is claimed or required by these
note-hash lemmas.

`SpendSemantics.of_production` composes these results with the unchanged
input-note extraction. Its `NoteFacts` conclusion contains bounded integer
balance, input membership/nullifier extraction, both output-note bindings
with their guards, and the withdrawal amount alias from `asset_holds_iff`.

`SpendExtraction.large_matching_extracts` applies this result to the actual
candidate returned by `MaskedSemantic.large_matching_extracts`. It keeps
literal R1 list membership, production constraints, and copy balance. All
opening, accepted-check, typing, matching-support, and bad-event premises
are unchanged. `strengthen_candidate_result` also accepts the already
checked `SemanticPrefix.large_matching_extracts_of_prefix` result verbatim;
there is no added premise asserting the output-note or amount conclusions.

## Remaining boundaries

The public-option shape is explicit, not inferred from `ProductionHolds`.
The typed Rust constructors populate those fields, but this checkpoint is
not their source-refinement proof. The withdrawal theorem gives the
field-valued public amount alias; converting the whole public codec to a
natural-number payment statement remains part of that correspondence.

The abstract append theorems are useful next steps, but their exact
transition premises still need to be derived from the current schedule,
copy, digest, and Poseidon gates, together with public prevalidation and the
source frontier invariant. The current semantic evaluator and the older
inactive residual evaluator are distinct Rust paths. Their relationship
must not be assumed from matching terminology. See
[`APPEND-REUSE-NEXT.md`](APPEND-REUSE-NEXT.md).

The generic FS2 theorem supports a parameterized round count; the old closed
masked instance has fixed D2/D3 boundaries and a five-round opening. The
new 33-round instance still needs its own obligations. See
[`FS-REUSE-NEXT.md`](FS-REUSE-NEXT.md). Neither this semantic strengthening nor
the reused theorem gives a new probability bound. Shared-oracle accounting,
authenticated source correspondence, universal masking/simulation, and the
final non-work-normalized security claim remain open.

## Focused verification

All six final targets passed on the NUC in the pinned workspace, each with
`MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, Lean's 5000 MiB threshold,
and zero recorded swaps. Every final axiom audit contains only `propext`,
`Classical.choice`, and `Quot.sound`.

| Target | Final attempt | Exit | Wall time | Peak RSS (KiB) |
|---|---|---:|---:|---:|
| `R1SpendValues` | a | 0 | 1.43 s | 3,319,320 |
| `R1OutputCopyLinks` | c | 0 | 2.27 s | 3,349,420 |
| `R1OutputNotes` | a | 0 | 1.78 s | 3,340,416 |
| `R1SpendSemantics` | a | 0 | 1.39 s | 3,328,660 |
| `R1SpendExtraction` | b | 0 | 1.50 s | 3,584,108 |
| `R1SpendCheckpoint` | a | 0 | 1.40 s | 3,568,284 |

The combined target imports both the new extraction and the previous semantic
prefix, with eight axiom audits. The two failed copy-link attempts exposed
small `Fin` projection/reduction details and were repaired with named finite
identities. The first extraction attempt unfolded the large candidate-list
definition during existential elimination; keeping the list definitions
locally opaque fixed it without increasing limits. These three failed
attempts and their exact source snapshots are retained alongside the final
receipts and object archive in `evidence/lean-spend-notes-20261013/`.

Source base: `65d5de037cf0acae9b15545ef88d9d5bb6800e0a`, plus the six
new source files pinned in the evidence manifest. Historical dependencies
were reused unchanged from the compiled cache. This is a focused component
checkpoint, not a new replay of the entire historical release manifest.
## Later append extension

[APPEND-GATE-BRIDGE.md](APPEND-GATE-BRIDGE.md) strengthens the same R1
candidate with the ordered output pair and literal append path. The
chronological tree, frozen-table recurrence, source refinement,
shared-oracle reduction, and privacy remain separate obligations.
