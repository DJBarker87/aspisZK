# Independent review by `/root/d18_point_weights`

This is an independent source/evidence review of `SelectedPrefixRead`; no
build was run.

`readAt_append_stable` is correctly stated with the sole explicit condition
`i < rs.length`: appending `tail` leaves the `i`th optional list lookup
unchanged. `readAt_sound` assumes a successful `readAt` and returns an
optional record at that index, its selected transcript-label equality, and
successful decoding of its data. It does not assert a table-consistency,
source-refinement, or acceptance property. These statements match the source
and the README's scope description.

Integrity checks passed: the bundle `SHA256SUMS` validates; the current
`SelectedPrefixRead.lean`, final snapshot, and attempt-a source all hash to
`6ecff471af039433f7ffe7103db006dc10c847b309ec3756c4c10bbb9eb02dab`; the
direct-import source `SelectedIndexedRead.lean` matches its pinned hash
`0c44871e4c84fc545381a6df9bb2d8fa23102f4d2af229da2b6600fa56003b35`; both
compiled archive members match manifest hashes and sizes; and the receipt and
log agree on exit 0, 1.47 s, 3,576,704 KiB peak RSS, zero swap, and the 4G/6G/0
cgroup. The log contains two axiom reports, each listing only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`.

No discrepancy was found in the reviewed theorem statements or evidence.
