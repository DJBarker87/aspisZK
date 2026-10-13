# ParentSupport focused Lean receipt

`lean/ParentSupport.lean` proves finite-index and cardinality facts for the
four-lane parent map. For a flat support `M`, it defines its parent image,
shows `M` is contained in the full quartets above that image, proves each full
quartet set has cardinality `4 * |S|` through `fibreIndexEquiv` and
`repeated_support_card`, and derives `|M| ≥ 9558 → |parentSupport M| ≥ 2390`.
The final theorem specializes the arithmetic to width `4 * 65536`. These are
support/index lemmas only; no decoder or cryptographic premise is introduced.

The final source SHA-256 is
`f5993b2950e70058e25368f9fec84d031a2afefbaec0f1efee2c7e6239a2e733`, from
worktree revision `31b6f19270a3e6463a2a4d92a058042cdf95cdce` (uncommitted
source). It imports only the focused modules `R1NaturalProjection` and
`R1RepeatedLift`, plus the Lean core Omega tactic. Their source hashes are
`add9c506d5cbf5c55447c9df156a52eb2298fe5ecf53faff2ea6a9654152726a` and
`bb5fa533f56b5b9c7adc84970cad149dfb0e4eccab4820f8fa4cbea74a996605`.

The focused target was `R1ParentSupport` in
`/home/dombarker/project-offloads/aspis-fs-generic-20261006` on the pinned NUC
Lean 4.32.0 workspace:

```sh
./run2.sh parent-support-r1-20261013b R1ParentSupport 5000 6
```

The run2 reservation check reported 24 GiB populated plus this 6 GiB scope;
the scope used `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`. Exit 0, wall
time 1.15 s, maximum RSS 2,193,328 KiB, swap 0. The cached module is at
`/home/dombarker/project-offloads/aspis-fs-generic-20261006/objects2/R1ParentSupport.olean`.
All eight printed axioms were `[propext, Classical.choice, Quot.sound]`, with
no `sorryAx`. The Lean environment manifest SHA-256 was
`ad7b87bbcfd84dc762927729c3d35a1822a530e57538a58c9d559f6ec4b6754e`; Lean
git hash was `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.

Attempt A compiled the same module before adding the explicit
`parentIndex_mem_of_mem_fullQuartetSet` projection lemma; its source hash and
receipts are retained in `remote-evidence/`. Attempt B is the final source.
The final source snapshot, `.olean`, stdout/stderr, SHA receipt, and
`/usr/bin/time -v` receipt are preserved there.
