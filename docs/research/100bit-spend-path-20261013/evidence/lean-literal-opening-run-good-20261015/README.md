# Literal query sample and opening Good evidence

This bundle contains two focused targets. `LiteralQuerySample.valid_row31_success_decodes` uses the existing Q22 scanner invariant to show a successful row-31 query list passes `LiteralQueryRead.decode`. `LiteralOpeningRunGood` derives nonzero gamma from the actual all-byte sampler and concludes the existing `Good` predicate under successful terminal reading and the theorem's no-hit condition.

The QuerySample green compile reports two standard axiom reports and took 1.68 seconds (3,583,116 KiB peak RSS, zero swap). OpeningRunGood reports two standard axiom reports and took 1.97 seconds (3,618,940 KiB peak RSS, zero swap). Both used the pinned 4G/6G/0-swap/128-task cgroup. All failed attempts are retained.

Scope limits: these results do not prove successful terminal-reader coverage for accepted proofs, D3, Rust source correspondence, or a complete security theorem.

Base source revision: `b400d586a84383b19f6250c383d56db1dda0a622`.

Loose object copies have been checked byte-for-byte against the matching archived members and moved outside the bundle to `/tmp/aspis-r1-retained-loose-objects-20261015/`; the compressed object archive remains the bundle’s canonical object artifact.
