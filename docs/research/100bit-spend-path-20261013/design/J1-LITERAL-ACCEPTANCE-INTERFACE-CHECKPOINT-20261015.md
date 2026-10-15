# Conditional acceptance interface — 2026-10-15

`LiteralAcceptanceTerminal` compiles and reuses the checked transcript terminal
theorem and `GenericNoHitFS2.d3`. Its `Checks` structure collects explicit
reader, pairing, query/residual and semantic equations. It does not contain a
witness, Good, AcceptedPairing, matching-cardinality or no-hit field.

The three results are:

- A parsed public value and a successful spend check imply the literal spend relation.
- On the actual 33-round protocol transcript, `Checks` and no-hit imply a witness for that relation.
- An arbitrary verifier program satisfies terminal condition FS2 D3 **if** every accepted evaluation supplies `Checks` for its actual transcript.

The third premise is the remaining acceptance-to-model contract. This module
does not prove it for Rust, Pool, or a deployed artifact. Its protocol uses the
specification-level choice extractor; it does not prove efficient extraction
or the remaining Fiat–Shamir conditions.

## Evidence

Focused target `LiteralAcceptanceTerminal`, attempt `acceptance-terminal-a`:
exit 0; wall time 149.205 seconds; peak sampled process-group RSS 3,701,760 KiB;
0 process swaps. The three exported axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`.

Source base: `0a72c002472417fe1f715f9c8a91a8a5da6520bb`.
Source SHA-256:
`3126159ae620817735f0d8ff94e64f17a6155d693093b65ff30ba94c2447660c`.
Object SHA-256:
`8dad6d451eb291c28da8cb485d18e20da199822742991857de6ea0836429ae1f`.

The [focused bundle](../evidence/lean-literal-acceptance-terminal-20261015/README.md)
records the exact source, direct imports, cached dependency provenance,
runner, receipts and logs. The
[root artifact review](../evidence/j1-literal-acceptance-terminal-review-20261015.json)
independently checked manifests, source/object hashes, status and axiom reports.

## Release boundary

This closes a conditional terminal composition, not the requested security
goal. Current Rust semantic-loop correspondence remains absent from the
retained extraction artifacts, which cover field parsers. Commitment/Pool
correspondence, concrete sampler/query-budget correspondence, efficient
extraction, full probability composition, privacy and current runtime
certification remain outstanding. The next priority is discharging concrete
acceptance premises using existing checked components wherever they apply.
