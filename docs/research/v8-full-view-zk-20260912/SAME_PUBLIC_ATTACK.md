# Same-public raw separator and conditional q22 attack

**R15 scope correction (2026-09-19):** the source-valid raw separator below
does not, by itself, prove a full-transcript distinguishing advantage for the
generated performance path. That path is a fixed-witness, fixed-seed demo,
not the intended entropy-backed two-witness experiment. Its actual shared-
oracle/stopping/publication refinement remains open. The negative raw
regressions and the certificate are unchanged.

The two witnesses use the same note commitment in both input slots and
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
the raw public observations separate the two witnesses. To apply
`no_statement_only_simulator_of_pairwise_separator` to the intended real
experiment, one must still establish the event's **unconditioned source
probability**, including publication and every failure. The uniform-subset
number is not currently an established actual Aspis advantage. The universal
deterministic zero-extension theorem in `AspisV8R15/RawScheduleExtension.lean`
preserves the statistic for every injective 22-query schedule containing the
pair, but does not supply that probability.

One candidate repair is a pre-publication q22 legal-image/public-rank gate for the
complete conditioned witness-difference map, with fresh nonce/entropy on retry
and an accounted abort/retry law. The q18 Spend gate is insufficient because
the q22 path does not call it. A blacklist of `{4,6}` is only a diagnostic,
not a complete proof; adding mask directions for the selected-side ambiguity
is the more invasive alternative. Neither candidate is proved sufficient,
soundness-preserving, or authorized for production here. A valid repair must
address all disclosures and their retained posterior, not just this pair.
