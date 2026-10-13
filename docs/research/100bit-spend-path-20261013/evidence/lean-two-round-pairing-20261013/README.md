# TwoRoundPairing focused Lean receipt

`lean/TwoRoundPairing.lean` proves deterministic composition of the generic
radix-four pairing and the two-round comparison lemma. It derives both true
boundary identities and the final evaluation equality from `round_boundary`
and `round_eval`, then applies the comparison result and cancels the explicit
nonzero quarter factor. The two included bad-set bounds instantiate degree at
most 6 and candidate-list size at most 100, giving 600. This adds no extraction,
causality, source-semantics, sampling, or security premise or conclusion.

The successful source SHA-256 is
`6eb9bd12b1190d1f0975bc4b70651afe4c55d082e860432057d27bcb577b3cc5`.
It was compiled as target `R1TwoRoundPairing` from
`/home/dombarker/project-offloads/aspis-fs-generic-20261006/sources/R1TwoRoundPairing.lean`
with:

```sh
./run2.sh two-round-pairing-r1-20261013f R1TwoRoundPairing 5000 6
```

The pinned NUC runner reported populated reservations of 24 GiB plus this
6 GiB scope; scope properties were `MemoryHigh=4G`, `MemoryMax=6G`, and
`MemorySwapMax=0`. Lean's memory limit was 5000 MiB. The target exited 0 in
0.97 seconds with peak RSS 2,215,104 KiB and zero swap. The cached module is
`objects2/R1TwoRoundPairing.olean`, SHA-256
`06cfeefa06501c94a2d25784e4f49113d68e9a1312443d449991d36e5d9f9f76`.
The three printed theorem axiom lists were all
`[propext, Classical.choice, Quot.sound]`; none includes `sorryAx`.

The imported cached modules were `R1RoundPairing` (source SHA
`1c03d1bb7d9360207bbc20f1b293a8e2de4c550c237fe3eb9d56713bf7e16797`, olean
SHA `fee1c264cafd8b6e1e96491e9e04a0354121c44796fcde9cf5f1b4ecc7b590fd`)
and `R1TwoRoundComparison` (source SHA
`781f9d979760e55cdade84ddf597f226ca2f7f9a44ed3dfd1189a27640f3933e`, olean
SHA `15cb2a8e4f95836d9bbacded157bc21925c4ac990aaaf8d4277485a11a5da1c4`).
The pinned environment manifest SHA is
`ad7b87bbcfd84dc762927729c3d35a1822a530e57538a58c9d559f6ec4b6754e`; Lean
revision is `8c9756b28d64dab099da31a4c09229a9e6a2ef35`. The local base revision
was `a29d480477dd7ad3e2d2343f71baa2b4ef91a3df`, plus the uncommitted new
source.

Five earlier focused attempts failed while fixing type inference and proof
plumbing. Their exact logs, `/usr/bin/time -v` output, and source-hash receipts
are preserved under `remote-evidence/evidence/` as attempts `a` through `e`;
their source hashes were respectively:

```text
1e3768ffc3676f41b74dde0b90d0e20dcb30699eed1bd9bfe295df6c49ad1fcd
9dc97d782fbd52f8f68ee3909bc9bef60d04d85ae18c32ebf65554f659422cac
69ebe56608619d4e9824feb5873c1e9531b03483adeaadf98aa5f1878f3bf902
9b67b5eac4c39a2bae12c8f4b072ea335391c5b65729d916286d0b389c54877e
10aaadf52e225b1862f7014850374e245694cf6272d213ad9125d32595054d7f
```

The successful source snapshot, cached `.olean`, and all six attempts' exact
Lean output, time, and hash receipts are retained in `remote-evidence/`.
