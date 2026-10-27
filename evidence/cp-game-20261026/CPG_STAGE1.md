# Four-field game and entry inversion

CPG_Game.DeployedPairExecution has exactly four fields, each quoting the
amendment verbatim. The data carrier CPG_Projection.Observations has only bank,
layout, adjacency, intervening key labels, final reply, copied buffer and ordered
action data. Entries are transaction-boundary cached bank projections, with a
single global bank key namespace. The recorded action pair is the checkpoint
copy and its ordered suffix through final parent completion; the history segment
is after that copy and before TX2 entry, so it excludes the initial save itself.

No history equality or ordinary eligibility is a game field. Conservative
ordinary eligibility excludes all signing and all system-owned accounts; this
is narrower than excluding only fee payer/durable nonce. The explicit verifier
program != system program pin is needed for an arbitrary program parameter.
This restriction and its runtime meaning must remain visible in the final trust
and ledger audit. These are checkpoint-projection semantics, not a new proof of
the deployed validator implementation.

CPG_Accepted derives positive writer/reader funding from actual native acceptance
and the existing extraction boundary. Writer flags and owner checks derive the
conservative ordinary predicate. No fee/nonce exception is assumed eligible.

Attempts 1 and 2 were elaboration failures (untyped conditional projection,
then missing definitional reduction); recovery sorryAx output is EXCLUDED.
Corrected projection passed attempt3; game passed4; accepted lemmas passed5.
No timeout, memory kill, cap raise or unchanged rerun. Each successful theorem
uses only propext/Classical.choice/Quot.sound. Full target/revision/source/deps,
exit/wall/RSS/swap/cgroup/axioms are in per-attempt receipts. Budget5/100 Lean,
0/20 Kani; same pinned SInt2 cache, unchanged launchers, one capped scope at a time.
No source/artifact adoption, shipped file, wire, feature, toolchain or ELF change.
