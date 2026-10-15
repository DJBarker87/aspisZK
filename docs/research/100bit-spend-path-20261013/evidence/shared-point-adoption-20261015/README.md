# Root-reviewed shared-point adoption

The runtime `weights.rs` now exactly matches the isolated, tested candidate
`68c9087712ff6bfb08c7ed41a1281798466e6671800761c80f83126963262f63`.
The tested SBF ELF is `7cf2fb3e7fe3a1237d508b0d3a2629d8cf1229ebf0e22c39ab236cd9a9dd255a`.
This is adoption in the research branch, not a protocol security release.

Root inspected the code, the generic contraction proof, the differential
harness, and all five matched settlement outcomes. For canonical field inputs,
the old tensor at index `16*s+j` is the product of the `d2` factor at `j%4`,
the `d3` factor at `j/4`, and the `d4` factor at `s`. When the explicit equality
guard holds, rows 0 and 2 share the first two factors. Distributivity permits
four shared 16-term partial sums and two separate four-term contractions.
Each row retains its original `d0/d1` scale. The other functionals, kappa
combination, fallback, field types and challenge schedule are unchanged.
Every new accumulator has at most 16 terms, within the existing 4096-term cap.

`SharedTensorContraction.contract_pair` proves the algebraic regrouping over
any commutative semiring using existing sum/distributivity lemmas. It is not
an extracted Rust proof. The corrected finite differential explicitly tests
nonzero unequal scales `1/16` and `6/16`; the initial manual test accidentally
zeroed both scales, so its original evidence is retained and superseded for
that case by the separate scale-fix bundle. The implementation did not change
between those test runs.

The matched 13-pair transfer saved 66,896 settlement CU; stage one and
transaction sizes were unchanged. All four larger transfer/withdrawal cases
passed, including rollover account and balance checks. They reused the exact
earlier OS-random-mask proof bytes. No claim of universal cost or new entropy
draw is made. Source manifests, unchanged stack diagnostic comparison, raw
receipts and exact hashes remain in the sibling measurement bundles.

`adoption.json` records the checked evidence indexes and exact source pins.
The candidate measurement bundles retain their historical pre-adoption
status; this later record is the adoption decision. No wallet keys are included.
