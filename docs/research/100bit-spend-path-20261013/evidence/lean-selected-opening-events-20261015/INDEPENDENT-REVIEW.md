# Independent evidence review

The event module defines the four selected sets by direct application of
`ConcreteBinding.gammaBad`, `kappaBad`, `firstBad`, and `secondBad` to the
staged payload values. Its four card theorems reuse the matching existing
`ConcreteBinding.*Bad_card` results with the same explicit `W`, `V`, `F`,
`F0`, and challenge arguments. The first and second card results require
degree at most 6; `OpeningPolynomialView.firstPolynomial_natDegree_le` and
`secondPolynomial_natDegree_le` discharge those premises from the respective
seven-coefficient payloads.

The successful event attempt is `R1SelectedOpeningEvents-a`: exit 0, 2.28 s,
3,580,844 KiB peak RSS, zero swap, cgroup 4G/6G/0. Its source SHA-256
`33f96fa95ab309db7ae7f5959b556032c2574d7e7e1449aca40a06d5e48f1949` agrees
with the receipt and final snapshot. The log contains four public axiom
reports, all listing only `propext`, `Classical.choice`, and `Quot.sound`.
The five archived objects match the manifest's names, sizes, and hashes.

The manifest initially referred to four import snapshots without their actual
`R1` filename prefixes. Those snapshot paths now match the files in
`import-sources/`; source hashes and Lean sources were not changed. The
source-path validator checks all five manifest target sources successfully,
and the complete bundle checksum list verifies.

This review covers the fixed-input set/cardinality interface only. It does
not establish causal recovery, a D2 bound, or source correspondence.
