# Reusing the concrete input witness

The R1 joint-list candidate now supplies one concrete input relation:
ownership commitment, nullifier, membership path, a valid input pair and an
occupied selected slot. The pair's other commitment equals the first path
sibling. Thus the occupancy facts refer to the pair actually authenticated
by that path.

## What was reused

The old `R0P.input_note_extracted` proof already used `traceSk`, `traceSalt`
and `tracePath`, but its existential conclusion hid those choices. The added
`R0P.input_note_trace_witness` exposes those exact witnesses under the same
six schedule/path/digest/asset/Poseidon/copy hypotheses, reusing the old
private extraction lemmas. Removing only the added declaration and its
axiom print restores the historical file byte-for-byte. No existing theorem
statement or proof body changed.

`InputWitnessCore.trace_sibling` reuses the input-pair copy/path equations.
`pair_head` proves that the first membership step hashes the exact ordered
pair. `InputWitness.of_production` joins those facts with the historical
witness and the occupied-slot theorem. `bounded_of_production` also reuses
the value theorem: the three natural values are below 2^30 and satisfy
integer conservation, with the input commitment using that same value.
It does not assert strict positivity.

`InputWitnessExtraction.strengthen_candidate_result` preserves the same
member of the R1 joint candidate list, its production/copy constraints,
output-note facts and chronological afterstate, and adds this concrete input
relation. It retains the existing opening/semantic premises, authenticated
old-frontier invariant and non-carry public-check premise.

## Focused verification

At base `df240a6cda47343b7e50bd4f7e4900ea6f431f65`, all five targets passed
on their first attempt on the pinned NUC. The combined checkpoint took
1.51 seconds at 3,591,584 KiB peak RSS with zero swap and six axiom reports,
all limited to `propext`, `Classical.choice` and `Quot.sound`. The largest
target used 3,608,488 KiB. Each scope used `MemoryHigh=4G`, `MemoryMax=6G`,
`MemorySwapMax=0`, with Lean 4.32.0 at
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`.

The [manifest](evidence/lean-input-witness-20261014/source-manifest.json)
retains receipts, exact source snapshots, final objects and the historical
pre-edit source/object. The [root audit](evidence/lean-input-witness-20261014/ROOT-VALIDATION.json)
independently verified all source and object hashes, resource logs, standard
axiom reports and byte-for-byte historical restoration. No unchanged full
manifest replay was run.

## Remaining boundary

This proves membership in the public anchor through a 24-level path in the
field model. It does not prove that the anchor is an authorized historical
root read from the actual program accounts, nor that Rust/account decoding
and settlement implement these modeled guards. The actual 33-row
Fiat–Shamir instantiation and complete privacy proof remain open. This
bridge alone is not a 100-bit spend theorem.
