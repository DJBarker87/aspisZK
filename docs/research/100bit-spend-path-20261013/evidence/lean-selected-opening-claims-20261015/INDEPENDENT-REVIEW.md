# Independent review by `/root/d18_point_weights`

Reviewed the source and all seven attempt bundles read-only; no build was run.

The current `Y` vector has the six requested positions: row-25 point claims
0–2, row-25 extra at index 3, row-26 `beforeZ1` at index 4, and row-27 gamma
payload at index 5. Each entry is the value of its `LowWide` subtype. The
index lemmas identify those six positions directly, and `Y_im_zero` uses the
stored subtype property for each position. The private generic
`weighted_parts` lemma decomposes the seven-term kappa sum into the constant
`c0` and six gamma-weighted vector sums; `parts_weighted_sum` specializes it to
`Y` and the existing `JointFunctionalBinding.claimedValue`. This checks the
mathematical identity stated in the source; it does not identify the supplied
payloads with source execution or accepted proof data.

Attempt snapshots match all seven manifest source hashes. The six failed
attempts each retain six axiom reports: attempts a and b have `sorryAx` in all
six, while c, d, e, and f each have `sorryAx` in only the
`parts_weighted_sum` report. Thus the failed attempts contain 36 reports and
16 reports with `sorryAx`. They are diagnostic failures, not accepted theorem
results. Green attempt g has six reports, all listing only `propext`,
`Classical.choice`, and `Quot.sound`; its receipt records exit 0, 2.21 s,
3,586,452 KiB peak RSS, zero swap, and the 4G/6G/0 cgroup. The current source
matches the final snapshot. Every object archive member matched its manifest
hash and size, and the existing `SHA256SUMS` passed before this review was
added.

The import caveat in the bundle is accurate: `R1JointFunctionalBinding`
source was not present in the compile workspace. Its pinned source and
previously archived object are included, and the bundle does not assert that
the source/object identity was checked at compile time.

No discrepancy was found in the six-position mapping, helper identity, or
final-attempt evidence.
