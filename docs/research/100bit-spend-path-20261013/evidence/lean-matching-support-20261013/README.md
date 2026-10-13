# MatchingSupport focused Lean result

`R1MatchingSupport` packages the supplied `R1ConcreteBinding.binding`
premises. Under its exact challenge/bad-set exclusions and accepted final
dot-product plus two boundary equations, 9558 matching original positions
imply the deterministic literal-candidate and functional claims. Its
contrapositive gives a 9557 support cap when those claims fail. The last
corollary applies the existing without-replacement theorem only to the ideal
uniform ordered-injection sampler for 22 queries. It makes no deployed
sampler, random-oracle, work-factor, or protocol-security claim.

The final source is
`docs/research/100bit-spend-path-20261013/lean/MatchingSupport.lean`,
SHA-256 `a3f4eed1b103cdc9cf8b92a3d37a313759e1324a04af79dc251dad8cde775a5b`.
It compiled as target `R1MatchingSupport` in the pinned NUC workspace
`/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013` with:

```sh
bash compile-one.sh R1MatchingSupport f
```

Attempt f exited 0 in 1.46 s, peak RSS 3,151,772 KiB, swap 0, with
`MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, and the runner's 5000 MB
Lean threshold. `#print axioms` for all three main theorems reported
`[propext, Classical.choice, Quot.sound]`. The compiled object is
`/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013/objects/R1MatchingSupport.olean`.

The workspace base revision was `3638d7546f6e03a1afb0eaabdb1cff38d1631e84`;
the target source hash above records the dirty file used in the compile.
Attempts a–e and f are all retained here with exact source hashes, receipts,
logs, and timing/resource records. Attempts a–e exited nonzero while source
plumbing was corrected; no cap was raised.
