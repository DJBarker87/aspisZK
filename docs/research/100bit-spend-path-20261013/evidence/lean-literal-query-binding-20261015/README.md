# Literal query/rho event-binding evidence

This bundle preserves four focused NUC attempts for three reviewed Lean targets:

- `R1LiteralQueryBinding-a` failed during proof elaboration and emitted one `sorryAx`-bearing axiom report; `R1LiteralQueryBinding-b` succeeded after the proof correction.
- `R1LiteralQueryCurrentRead-a` succeeded.
- `R1LiteralRhoBinding-a` succeeded.

The three successful attempts emitted three axiom reports total. Each reports only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. All attempts used the recorded 4 GiB high / 6 GiB maximum cgroup with swap disabled. The manifest records each exact source snapshot, receipt, log, timing, resource report, source base, and successful declaration audit.

The query binding equates a row-31 event with a finite-set event only under explicit validity, decoded matching-data, and strict-query-reader premises. The rho binding likewise requires successful matching-data and query readers. These are conditional representation identities; this bundle makes no acceptance, extraction, source-refinement, or security conclusion.

`literal-query-binding-objects.tar.gz` contains the three target oleans and the four direct-import oleans. Transitive dependencies are identified by the pinned runner environment and its shared Lean cache. No loose `.olean` files are retained in this evidence directory. `source-manifest.json` records source and object hashes; `SHA256SUMS` covers all bundle files other than itself.
