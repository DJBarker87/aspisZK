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

Stage 2: P6 preflight and checked counterexample.
- Kani names were listed before use. equal_raw and keep_clear_raw passed.
- scan_1024_raw timed out at 240 s; it is not rerun. No op258 source-law
  credit, and no generated reference extraction/Lean closure is claimed.
- Proposed op121 P6 ROW: for every raw [QM31;28] polynomial and QM31
  challenge, shipped radix-four source equals existing Horner reference.
  The optimized native preflight refutes it: only coefficient 2 = (1,0,0,0),
  challenge = (0,2147483648,0,0), source = (3,0,0,0), reference = (P-1,0,0,0).
- Kani default checks confirm source CM31.square subtraction overflow on that
  input. --no-overflow-checks does not suppress that MIR assertion; it also
  fails, and is not claimed as wrapping-semantics verification. A separate
  reference-only harness passes all 134 checks with exact output P-1.
- Every host aspis-core Rust source matches the worktree SHA256. No source
  was fixed, no canonicality premise was added, and this is not claimed as a
  counterexample to either admitted fixture or the privacy endpoint.
- Per the user's checked-ROW-counterexample stop condition, stop substantive
  proof work now. The remaining three Lean invocations are final audits.
  Kani budget used: 6/6 (3 passed, 2 arithmetic-failure reports, 1 timeout).
- rw20 checked again at c5c41653d7: only ProverRw19 modules, explicit missing
  concrete input-to-model map. Fixture byte equations stay exact/open.
- Inventory remains 30; zero new source laws, zero rows universally excluded
  from both fixtures. Six native-effect entries explicitly deferred in
  inventory.json; deferral earns no premise-removal credit.

Final stage: attempts 36802, 36803, 36804 passed, respectively 64, 63 and
128 axiom reports. Last three actual Lean invocations reserved for audit.
All new and inherited PV_Join theorem statements were printed in the two
portions, and all axioms audited in the final combined target. Source revision
6386cb7f6d; no release-manifest replay. Pinned Lean cache retained; own new
pole-target Cargo cache removed. The timeout's complete child RSS peak was
not retained; its receipt explicitly records the live lower bound and GNU
time limitation rather than treating wrapper RSS as aggregate RSS.
