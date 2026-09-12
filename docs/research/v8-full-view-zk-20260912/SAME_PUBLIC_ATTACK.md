# Same-public q22 attack

The current q22 performance path fails the intended full-view adaptive-ZK
claim. The two witnesses use the same note commitment in both input slots and
differ only in `selected_second`; public statements and snapshots are
byte-identical, and both transfers pass.

The actual encoder changes only row 913 (column 0) and row 1017 (column 10).
For q22 fibres 4 and 6, the retained separator
`[1508290849,1480589898,639192798,666893749,2147483646,0,1,0]`
annihilates every relation-free column-0 mask cell but evaluates to
`490597912` on row 913. The full functional values are `1959911333` and
`303025598` in M31. Real mask application with distinct seeds preserves them.

For uniform distinct q22 sampling from 262144 fibres, the event containing both
4 and 6 has exact probability `11/1636171776` (about 2^-27.15). On that event
the public view separates the two same-public real laws. The formal theorem
`no_statement_only_simulator_of_pairwise_separator` therefore rules out a
statement-only simulator at the intended privacy level.

Smallest repair: add a pre-publication q22 legal-image/public-rank gate for the
complete conditioned witness-difference map, with fresh nonce/entropy on retry
and an accounted abort/retry law. The q18 Spend gate is insufficient because
the q22 path does not call it. A blacklist of `{4,6}` is only a diagnostic,
not a complete proof; adding mask directions for the selected-side ambiguity
is the more invasive alternative.
