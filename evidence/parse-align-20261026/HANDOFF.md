# Parse alignment handoff — budget exhausted

**Outcome: 0/2 requested whole WhenBound premises removed.** No checked counterexample against shipped source was found. Stop condition is 100/100 actual Lean compile attempts; 0/20 Kani runs. No Uni_Accepted composition is claimed.

Branch `codex/cx-parse-align-20261026`; private host workspace `/home/dombarker/project-offloads/codex-cx-parse-align-20261026` on `dombarker@100.108.41.90`. Only prefix-owned new Lean files and this evidence directory changed. Stage commits are local; no push.

## Before/after and ledger delta

Before: `PSem_Accepted.accepted_pair_claims_semantic_rows` derives semanticRows27 on the accepted TX1, but returns `Tx1Q_Endpoint.WhenBound run`. That definition still takes, for the SAME parsed/q/tr/data:

1. `parseReached (bytesOf proof.val) tr = some parsed`;
2. `LiteralMatchingData.read (typedRows parsed q tr) = some data`.

After: `PAln_Accepted.accepted_pair_selected_physical_rows` preserves the predecessor's accepted-pair input hypotheses and inherited conditional conclusions, strengthens the existential FirstCut to the semantic public value actually selected by its native selector, and derives `PAln_JoinedFacts.Facts` on its SAME run. It still returns the SAME WhenBound. The source cuts and reader-existence continuation are derived conclusions, not replacement premise structures. Full before/after types, WhenBound and the complete Facts definition are printed in passing attempt104. Attempt101 also prints the final accepted theorem and its axioms.

Ledger rows REMOVED: **none**. Rows ADDED as assumptions: **none**. L099 (`entry.parsed`) and L165 (full semantic/transcript join) remain OPEN in their whole-source sense. No new ledger ID is allocated for the implementation subgoals below. The independent matching-data read gate remains OPEN. No source gap is reclassified as external trust or cryptography. The authoritative shared ledger was not edited.

## Checked prerequisites

- `PAln_JoinedRun.on_run` and `PAln_JoinedFacts.on_run`: actual compact semantic expansion, physical C1 root, strict semanticRows27, public initialization, ordered first25 calls and their record frames, both circle calls, physical Y1 expansion, source-selected view, all opening suffix calls, returned preparation and scratch, all on ONE run.
- `PAln_SelectedAccepted` / `PAln_Reselect`: native semantic selector's value used as FirstCut semantic witness; writer transport preserves the old accepted-pair conclusions through the actual returned checkpoint.
- `PAln_Public.from_cut`: actual public serializer output parses, using the native selected public cut. `PAln_Bootstrap.on_run` discharges the canonical constructor's public/tag/root inputs on this cut.
- Physical rows: Y1 compact range7031..7495 expands to row27; actual row28 input is7495..7527 and parses to the selected inactive carrier (`PAln_InactiveDecode.physical`); round0/round1/final ranges are7527..7751,7783..8007,8007..10055. Both actual Vec extensions concatenate folded-root bytes7751..7783 with round1 for row30 (`PAln_CurrentPhysical.second`).
- `PAln_OutputFields.from_double`: actual scalar calls return the same gamma/kappa/alpha values stored in the returned preparation. The preparation equation also retains actual queries/rho/final state.
- Strict decoder proofs construct all semantic and opening row payloads from canonical bytes and compact zero insertion. `PAln_Carrier.parser_and_data` proves Aligned, parser success and existence of literal data for the canonical33-row constructor. `PAln_ReadFields.alpha1` identifies a successful read's alpha1 with its row30 ordinary carrier.
- `PAln_Oracle` uses the EXISTING digest extraction, P1 and success-conditioned RuntimeSyscall laws for the installed digest. `PAln_Log.source_replay` uses SdkC_Source/SdkC_Oracle to retain first25 reached digest inputs in order, including duplicates. This is not the complete transaction oracle history or a counterfactual-oracle transport.

## Exact remaining join

The canonical constructor deliberately takes six suffix values and eight states, queries and rho as parameters. Bootstrap proves parser/read existence for those carriers; it does NOT identify them all with the actual circle/opening returns or prove their entire source/oracle interpretation. Consequently those proofs are not gate elimination.

Next bind the circle returns and opening challenge/queries/rho carriers to that one constructor, prove row28 original serializer bytes equal its actual parsed input, and identify the complete literal read (semantic functionals, Y, inactive, round/final polynomial payloads and challenges) with the data related to `run.p` by SessionAPrepare. Existential reader success alone does not establish equality to arbitrary SessionAPrepare data. Retain source initialization and all ordered oracle calls throughout. Only after these joins specialize WhenBound with both parser/read facts and remove its two gate arguments in an accepted-pair result.

## Non-vacuity and success conditioning

The accepted extension adds no input hypotheses; every extra source cut is derived from the same successful native pair. Thus it introduces no new admission premise that could manufacture vacuity. Existing `Tx1Q_Nonvacuity` local extraction/initial-pending witnesses and their PSem audit099 are reused, not rerun. They do not establish joint satisfiability of all native/runtime/cryptographic accepted-pair hypotheses. No new joint accepted fixture or whole33-row source witness is claimed.

All source inversions are success-conditioned. Rejection effects, complete oracle-history transport and the release security experiment remain open. Arbitrary suffix choices in the model constructor must not be reported as an actual source transcript.

## Validation and freeze

100 actual Lean invocations:63 passes,37 retained elaboration failures; six invocations build missing unchanged log dependencies. IDs010,011,096,102 did not invoke Lean (launcher admission failures or a never-run config) and are excluded. Attempt060 had a shell flag typo before its one corrected actual invocation. No wall timeout or memory kill, cap increase, unchanged timed-out retry, package replay, Rust/SBF build or Kani run occurred.

Every invocation used the unchanged S2W host launchers and a single module, `lake env lean -j1 -M7000 -DElab.async=false`, own scope with MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64, at most one8GiB reservation at a time. Final host scope inventory has only init.scope; all our jobs are terminal. Job swap0 throughout; peak recorded RSS5,214,500KiB. The host has unrelated pre-existing swap usage; it is not attributed to these no-swap scopes.

`validation-attempts.jsonl` retains exact target/command, source hash/snapshot, dependency fingerprint, actual revision anchor, exit status, wall time, RSS, swap and full axioms lines for every invocation. `validation-summary.json` lists every final source and matching successful receipt. All final Lean files match successful source snapshots. Original anchors are preserved; no old run is attributed retroactively to a later commit. `final-host-pins.json` records object/source and launcher hashes; it also preserves obsolete diagnostic objects in the private workspace, which are not final source targets.

Final attempt104: exit0, wall2.265831272s, peakRSS5,200,396KiB, swap0, source anchor da8607f120 plus exact dirty source SHA in its receipt. All audited top results use only `[propext, Classical.choice, Quot.sound]` (or subsets). Failed diagnostic sorryAx output is retained and excluded. No new sorry/admit/axiom/native_decide, heartbeat/depth override or reducibility override occurs in final modules.

`source-pins.json` rechecks the five inherited shipped Rust source hashes against this checkout. Coherent SInt2 and pinned PSem objects, including SdkC_ source/oracle objects, were reused. No new release replay is asserted. No shipped file or cfg(kani) module changed, so the three ELF rebuild trigger did not fire. Inherited pins, NOT newly reproduced:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

No account/key action, Session A worktree/candidate edit, release artifact change or shared object overwrite occurred. No binary, ELF or archive is committed.
