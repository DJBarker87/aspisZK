# RoundPairing focused Lean receipt

`lean/RoundPairing.lean` contains a generic, field-level radix-four round
pairing. It defines the source permutation `[0, 3, 2, 1]`, the quarter-scaled
dual fold, the specified round polynomial, and the primal/dual Horner forms.
It proves the degree-six bound, polynomial evaluation identity, coefficient
boundary relation, and the boundary-claim cancellation under explicit
`(4 : K) ≠ 0`. These are algebraic identities only; the file makes no
source-semantics or multi-round soundness claim.

The final source SHA-256 is
`1c03d1bb7d9360207bbc20f1b293a8e2de4c550c237fe3eb9d56713bf7e16797`, from
worktree revision `31b6f19270a3e6463a2a4d92a058042cdf95cdce` (uncommitted
source). It imports the cached `R1NaturalProjection` index definitions and
narrow polynomial/tactic modules. The `R1NaturalProjection.lean` source SHA is
`add9c506d5cbf5c55447c9df156a52eb2298fe5ecf53faff2ea6a9654152726a`.

The focused NUC target was `R1RoundPairing`, command:

```sh
./run2.sh round-pairing-r1-20261013b R1RoundPairing 5000 6
```

The runner reported a populated 24 GiB reservation plus this 6 GiB scope;
the scope used `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`. Result:
exit 0, 1.49 s wall time, maximum RSS 2,206,328 KiB, swap 0. The cached module
is at
`/home/dombarker/project-offloads/aspis-fs-generic-20261006/objects2/R1RoundPairing.olean`.
All eight printed axiom sets were `[propext, Classical.choice, Quot.sound]`,
with no `sorryAx`. The environment manifest SHA-256 was
`ad7b87bbcfd84dc762927729c3d35a1822a530e57538a58c9d559f6ec4b6754e`; Lean
git hash was `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.

Attempt A is preserved with its exact source SHA and failed proof log; it
failed only in the dual-Horner normalization. Attempt B is the successful
source. Both logs, source-hash receipts, the final source, `.olean`, and
`/usr/bin/time -v` receipts are under `remote-evidence/`.
