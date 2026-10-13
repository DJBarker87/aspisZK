# NaturalProjection focused Lean receipt

This focused module proves source-level natural-basis evaluator identities for
a four-lane sparse lift and fibre-mean projection. It uses the exact
`naturalLineValue_four_mul_add` identity. It does not prove a protocol or
encoder security property, and it does not establish the bridge from
`naturalEval` to `naturalCoefficientPolynomial.eval`; that existing bridge is
left explicit for later composition.

The final source is
`lean/NaturalProjection.lean`, SHA-256
`add9c506d5cbf5c55447c9df156a52eb2298fe5ecf53faff2ea6a9654152726a`, from
worktree revision `31b6f19270a3e6463a2a4d92a058042cdf95cdce` (uncommitted
source). The focused target was `R1NaturalProjection` in
`/home/dombarker/project-offloads/aspis-fs-generic-20261006` on the pinned NUC
Lean 4.32.0 workspace, with command:

```sh
./run2.sh natural-projection-r1-20261013e R1NaturalProjection 5000 6
```

The run2 reservation check reported 24 GiB populated plus this 6 GiB scope.
The scope used `MemoryHigh=4G`, `MemoryMax=6G`, and `MemorySwapMax=0`. Result:
exit 0, wall time 1.68 s, maximum RSS 2,211,924 KiB, swap 0. The cached module
is available at
`/home/dombarker/project-offloads/aspis-fs-generic-20261006/objects2/R1NaturalProjection.olean`.
No `sorryAx` appears in the successful target. Printed axioms were:

```text
laneCoefficients_sparseLift, sparseLift_injective, sparseLift_add, sparseLift_smul:
  [propext, Quot.sound]
naturalEval_radix4, naturalEval_zero, sparseLift_eval,
radix4ChildPoint_t2, radix4ChildPoint_t4, natural_fibre_sum,
naturalProjection_eval_fibre_mean:
  [propext, Classical.choice, Quot.sound]
```

The environment manifest SHA-256 was
`ad7b87bbcfd84dc762927729c3d35a1822a530e57538a58c9d559f6ec4b6754e`; Lean
git hash was `8c9756b28d64dab099da31a4c09229a9e6a2ef35`. The imported source
hashes matched the active worktree: `V5FriNaturalBasisRadix4.lean`
`0641318603afdaf3f1b1bf9b66c418da67049160973348468f4c3fafadefa4dd` and
`CircleNaturalBasisEval.lean`
`127ea451736936d8fb077e065efb7d49719af776b3782dc82af4b97076be3a9a`.

Earlier failures are retained under `remote-evidence/`: the initial polynomial
draft and an import-only diagnostic exceeded the 5,000 MiB Lean interpreter
threshold (each about 6,166,000 KiB peak RSS) before proof checking; the
lightweight route then had one unavailable Mathlib Omega object and two
proof-plumbing failures. Those attempts were not rerun unchanged with a larger
cap. The pre-lightweight polynomial draft is archived there as well. The final
source snapshot, `.olean`, stdout/stderr, SHA receipts, and `/usr/bin/time -v`
receipt for attempt E are preserved beside this README.
