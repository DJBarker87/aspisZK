# L187 Phase transport and coherent replay continuation

**S2/L187/L188 OPEN; target not yet established.** Branch
`codex/cx-replay-dry8-20261026`. Local commits only; no push/merge. Only
RPz7-prefixed sources and evidence in this job's directory are changed.

## Established repair

RPz7_PhaseIso explicitly maps all eleven producer verifier.Phase constructors
to FirstCaller.Phase and back, retaining every U8/Usize payload. Both round
trips, an Equiv, callback transports, optional-observer transports (including
None) and arbitrary observer-consumer transports compile at RPz7_001.
Their printed axioms are empty or [Quot.sound]. No nominal Type equality is
asserted or assumed. RPz7_002 checks the duplicate-alias-free replacement.

The original selected S1SemanticPhaseV1 has no theorems: its only declaration
is the conflicting abbreviation. RPz7_STAGE1.md gives its complete export
comparison table; the per-theorem restatement table is empty. Legacy S1 Phase
binders now explicitly use RPz7_PhaseIso.Phase, definitionally FirstCaller.Phase.
The producer retains its own distinct verifier.Phase. The exact sites are in
RPz7_phase-use-inventory.json. All original candidate files are untouched.

Concrete function-law checks and final budget/axiom results: PENDING.

## Checked composition checkpoint

RPz7_312 recompiles AspisR1.ClaimsUnrolledSdk.accepted_pair_claims on this
larger-producer/replacement cohort. Statement/proof body unchanged, import
names rerouted. Exit0,wall2.88s,peak5251716KiB,swap0; axioms
[propext,Classical.choice,Quot.sound]. Exact resources/pins are in the receipt.
This re-establishes an existing same-pair bridge, not a removed deployed premise.

The larger producer is the historical e5c186ba3 Tx1 extraction against which
the Tx1 bridge was actually proved. Neither producer has been shown to be a
complete extraction of frozen D188. RPz6 provenance is pinned/read-only; this
remains an OPEN provenance item. No source-to-ELF transfer is inferred.

## Actual top, ledger and non-vacuity

Actual root: AspisR1.Rc10_Top.deployed. RPz7_BEFORE/AFTER.lean.txt retain its
complete identical SOURCE statement (SHA256 fc89d7515e949c643df40078ebfd4322035ab120990aae686a8f0f621a34d8ff).
Complete before/after KERNEL comparison: PENDING, requires fresh top.

Premises removed/added/changed:0/0/0. Ledger method: actual plus deployment,
deduplicate L185=L159 and existing aliases, preserve classifications. Delta
T0/P0/G0/C0. Historical actual83T/12P/13G/0C and combined89T/16P/13G/0C
are unchanged; no fresh absolute kernel recount is claimed. No game, metric,
quantifier, failure event, conclusion or runtime trust item is adopted/changed.

No fresh joint deployment non-vacuity witness is available. Historical
conditional Rc10 witnesses retain their original scope; no stronger joint
inhabitation or extraction/runtime instance is claimed. The transport laws
add no security antecedent or hidden conclusion.

## Replay, audit and resource frontier

Final budget and frontier: PENDING. Initial root counts are in
RPz7_initial-root-frontiers.json. Larger-cohort valid reuse3128; original
union closure4964;1836 original modules initially need rebuilding. Even Rc7
alone initially needs1728 rebuilds, exceeding this round's1498 attempts before
new transport/audit modules. No top can be reached within this budget.

Every compiler uses the unchanged S2W runner, one admitted scope at a time,
MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64,Lean-j1-M7000-async=false.
Each receipt records exact target, command, source revision/hash, dependency
hashes, exit, wall, peakRSS, swaps, cgroup limits and complete printed axioms.
The 23 original resolutions and pinned Aeneas library base are inherited with
exact hash links; no first-found source substitution is used.

The 180 historical formatter records/85 nonstandard axioms are preserved
individually in RPz7_formatter-records.json. Fresh-top reachability: PENDING.
Partial-context audits cannot supply a yes/no result from an unavailable top.

## Artifacts and remaining work

No shipped Rust/Kani/SBF source, wallet/account key, ELF or other worker's live
worktree/candidate changed. No ELF rebuild trigger. Historical pins only:
default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

Next: continue the pinned fresh frontier, compile Rc7..Rc10, compare exact
kernel statements, audit fresh top/formatter proof-term reachability, then
close provenance/source-to-ELF and joint non-vacuity obligations. The 100-bit
release target remains unestablished.
