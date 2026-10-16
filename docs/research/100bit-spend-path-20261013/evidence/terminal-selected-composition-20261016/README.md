# Selected claims and terminal composition evidence

Twelve focused Lean 4.32 targets pass on the pinned NUC cache. Fifteen theorem
reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Five
source slices emit no reports and are counted only as successful compiles.
All twelve exit 0, with zero process swaps and maximum target RSS 3,821,512 KiB.

The generic Copy array helper succeeds when its callback succeeds and preserves
its captured state. The real 84-claim callback and four-word matrix-row callback
meet that condition: their concrete wrapper proofs derive it rather than
assuming it. The claim gather reads the first 28 cells from each of three
29-cell arrays and preserves canonicality of those selected cells. The row
wrapper derives successful execution and canonical residues from arbitrary
fixed U32 input arrays. It is not a whole matrix or permutation theorem.

Both actual candidate reverse-fold loops, of lengths 24 and 4, succeed on
canonical input arrays with a valid prepared multiplier and equal the existing
Horner model. The final composition theorem derives the prepared constructor
and both complete loops, then obtains the 29-lane polynomial. Canonical inputs
and identification of the arrays/seed with those lanes remain explicit caller
obligations. The array producers and enclosing terminal function are not proved
by this batch.

## Independent audit and reuse

`root-review.json` checks 394 original file checksums, all 41 attempt receipts
and raw logs, 12 selected output objects, 38 direct imports, and 18 exact
generated declaration blocks. Each custom import is reconciled to an already
published successful source/object pair; unchanged dependencies are not replayed.
Twenty-nine failed attempts are retained for diagnosis and contribute no proof
claim. Source snapshots in each selected receipt are authoritative; earlier
scratch drafts in the provenance kits are not selected successful results.

The generated slices come from G or the isolated Copy-helper/indexed-fold
candidate, as recorded per block in the review. They reuse the previously
checked selected-mask Types/Funs and arithmetic, row-callback, extension and
Horner theorems. `TerminalHornerModel` uses the existing symbolic arbitrary-length
sum proof, avoiding concrete recurrence reduction.

`proofs.tar.gz` contains the original bundle, all raw attempts, source/object
snapshots, runner, environment and provenance kits. The root audit additionally
archives exact G/candidate Funs/Types under `provenance/reviewed-generated`;
their hashes are in `root-review.json`. Original receipts and checksum files
are retained unchanged. After extracting, run:

```
python3 audit-bundle.py /path/to/bundle /path/to/aspis-repository
```

The repository supplies the already-published dependency evidence named and
hashed in the review. The audit does not invoke Lean.

## Resources and revision

Every target ran one at a time, with MemoryHigh=4G, MemoryMax=6G,
MemorySwapMax=0, TasksMax=128, Lean `-j1 -M5000`, async elaboration disabled,
and a 300-second timeout. The recorded workspace base is
`b40d1cfffadbdf967f84cca23ea4e7f1553d564f`; each new source and imported object
is separately hashed. The selected file contents are also maintained in `../../lean`.

| Target | Process wall time | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| CompositionPartsLoopAdapter | 0:02.57 | 3,000,196 | 2 |
| CompositionPartsLoopSlice | 0:01.23 | 2,602,520 | 0 |
| ArrayFromFnCopySlice | 0:01.23 | 2,600,520 | 0 |
| ArrayFromFnCopyStable | 0:01.40 | 2,612,060 | 1 |
| RawPoseidonExternalRowWrapper | 0:01.95 | 3,821,512 | 2 |
| RawPoseidonExternalRowWrapperSlice | 0:01.15 | 2,596,396 | 0 |
| SelectedClaimProofs | 0:01.95 | 3,015,244 | 7 |
| SelectedClaimSlice | 0:01.27 | 2,602,348 | 0 |
| SelectedClaimGatherStable | 0:01.63 | 3,004,732 | 1 |
| SelectedClaimGatherSlice | 0:01.21 | 2,599,068 | 0 |
| TerminalHornerModel | 0:01.39 | 2,985,668 | 1 |
| TerminalCompositionPolynomial | 0:01.48 | 2,992,656 | 1 |

No production Rust adoption, new CU result, complete terminal theorem, privacy
proof or complete 100-bit spend theorem is claimed. Candidate runtime comparison
and full source/semantic composition remain open.
