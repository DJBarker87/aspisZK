# Reusing input-pair occupancy and path gates

The same R1 extracted candidate now proves that the input pair is valid,
the first private path bit selects an occupied slot, and the selected
commitment is exactly the input-note hash block's output. This reuses
`V7PairLeafOccupancy` and the existing path, copy, schedule, and Poseidon
interfaces. No historical theorem or source file was changed.

## Literal bindings and checked facts

`InputPairCopyLinks` projects two always-enabled copy records from
`copyLinksAfterPositivity`:

| Record/tag | Exact binding |
| --- | --- |
| 0 / 1124073490 | The eight second-commitment cells at row 1017 equal the untweaked right input of compression block 4 (row 64). |
| 1 / 1124073491 | `A 0 913 = A 10 1017`: the first path side bit is the selected-side input to the occupancy gate. |

The second record's consumer pattern is pattern 7, whose column is 10. The
middle field of the endpoint descriptor is not a trace column.

`InputPair.leaf` uses block 4's left commitment, row 1017's occupied bit,
eight second-commitment cells, and occupancy inverse. The old occupancy
characterization proves `leaf.Valid`. The old node interface and first copy
record prove block 4's output is the compression of this ordered pair.

For selection, the occupancy gate gives
`A 10 1017 * (1 - A 0 1017) = 0`. The second copy record makes its first
factor the path's actual side bit. If the path chooses the second slot,
that factor is nonzero, so occupancy equals one. Choosing the first slot
uses the existing `first_slot_is_spendable` theorem. In particular an empty
second slot forces the first path bit to select the first slot; there is no
assumption that zero lacks a hash preimage.

`InputPairSelection.selected_output` then uses the existing path equations
and copy wiring to prove that the selected commitment is
`OutputNotes.output A 3`, the input-note hash block's output. This conclusion
is derived from gates and copy balance; it is not supplied as a premise.
`InputPairExtraction.strengthen_candidate_result` adds all these facts to
the same member of the R1 joint candidate list, retaining its output-note
and chronological afterstate facts.

## Verification and boundary

Five final focused targets passed on the pinned NUC, including one combined
checkpoint. The checkpoint took 1.39 seconds, used 3,592,484 KiB peak RSS and
zero swap, and reported nine standard-only axiom audits. Every run used
`MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`. The largest successful
target used 3,608,764 KiB. Lean was 4.32.0, commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`.

The [evidence manifest](evidence/lean-input-pair-20261014/source-manifest.json)
retains all 14 attempts, their exact source snapshots and receipts, and the
five final compiled objects. The integration base is
`7c740172da25ec986373b7c996a513b9d1c0ec11`; the unchanged copy-link source was
first compiled on the preceding `fd4aff50d` base. No full manifest replay
was performed.

The old input-note theorem supplies an existential secret/salt/path witness.
This new result fixes the selected slot to the literal trace path and hash
block. The next semantic task is to expose the old proof's already-used
concrete trace witnesses and assemble one theorem joining ownership,
nullifier, selected pair, and the complete authenticated forest path.
No full input/forest relation, Rust/account refinement, shared-oracle
Fiat–Shamir instantiation, or privacy theorem is claimed here.
