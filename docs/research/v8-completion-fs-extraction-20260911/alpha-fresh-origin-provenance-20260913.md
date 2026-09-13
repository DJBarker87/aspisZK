# Alpha fresh-origin provenance — 2026-09-13

## Result and evidence scope

The five fresh-origin leaves add deterministic provenance only.  An initially
absent lookup that is present after a `runMachine` segment is tied to a
matching `.fresh` history record, including actor, input, output, and
`freshTableEntryOfRecord` equality.  The source and pre-alpha insertion cases
retain those records, and the accepted-root/rooted projections preserve the
fresh disposition and the projected adversary-Q1 record case.

The evidence receipt is marked `PASS_DETERMINISTIC_ONLY` in
`results/v8-completion-fs-extraction-20260911/alpha-fresh-origin-provenance-v1/report.json`.
All five final sources were replayed separately on the Tailscale NUC under the
repository's cgroup policy.  They completed in 2.42--2.73 seconds with peak
RSS 6,624,192--6,735,480 KiB and zero swap.  `#print axioms` reported only
`propext`, `Classical.choice`, and `Quot.sound`; the first and fourth leaves do
not require `Classical.choice`.

An independent hostile statement review passed the formal causal content.  It
confirmed that insertion freshness is obtained from actual append-only table
extension and that the projected-root `priorTarget` branch is contradicted by
an actual adversary-Q1 record.  It also required the scope distinction retained
here: the four-way result is an acceptance-conditional deterministic origin
classification, not an event partition or probability theorem.

## Explicit remaining event/probability boundary

These leaves do not yet prove that the fresh-at-candidate branch is exactly
the complete eight-coordinate alpha sampler event.  Missing are:

- source alignment of all four output/advance pairs to the routed
  `RelationAlphaDuplexSlot` coordinates;
- a proof that every routed coordinate is fresh (rather than merely the first
  candidate lookup being absent);
- inclusion of prior/root/insertion cases in the exact causal target event;
- the measure-preserving pullback to the complete alpha sampler law and its
  probability charge;
- Fiat–Shamir composition, restoration success, payment extraction, and global
  soundness.

No probability term or conclusion-shaped event premise is introduced by this
milestone.
