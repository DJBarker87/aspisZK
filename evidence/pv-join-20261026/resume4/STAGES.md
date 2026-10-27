# pv-join4 stage record

Start: 1ad24470b8, branch codex/pv-join-20261026. Target not yet established.
Read the common rules, rulings (a)-(g), host restored flag, root AGENTS.md,
D42-D68 and D188, previous final report, and previous receipt index.
The existing report/index and green audit 36599 are reused, not rerun.

Budget: 100 actual host Lean compiler invocations, 6 Kani runs; IDs 36800-37099,
never reused. The last three compiler invocations are reserved for the new
combined audit. No local Lean. No shipped changes. No endpoint premise change.

Stage 1: source-reachability.json records all 30 syntactic dependency paths,
including callback/trait construction. This does NOT prove dynamic reach or
unreachability. Both fixture reach sets remain unresolved. No static absence
is available to justify dropping any row. S2 is fixed by the extracted client.

Sibling check: rw20 branch has only ProverRw19 modules and no concrete model
instance. cb4 op259_source is PREPARED and imports an unavailable Op259Funs;
no source-law credit. cb5 has no matching opN_source. No sibling edits.

36800 checks whether the standard library already provides the four vector
operations. It does not; the unknown-constant output is retained. This is a
failed inspection, not a theorem or a counterexample. P6 is required.

Next: focused P6 pole comparison reference and complete source rejection
prefix facts. Native effect rows 4 (generic Drop), 32 (fallible allocation),
122/123 (zeroization plus compiler fence), 232 (public checker timing), 257
(parallel/native host work and effects) are retained for pv-runjoin; none is
silently interpreted as a pure successful callback.
