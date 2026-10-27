# RPt coherent new-top replay

**In progress. S2 / deployed 100-bit target not yet established.**
Branch codex/cx-replay-tops1-20261027; original task text used suffix 20261026.
Local commits only; no push. Original source revision:
34b1c8fd70c608938f324f1fa6b74e98f2471bd0.

## Scope and cache

Continuation of the RPz8 coherent cohort in
`/home/dombarker/project-offloads/codex-cx-replay-dry-20261026`.
No duplicate workspace or package replay. Pinned Lean 4.32.0:
`/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0`.
The ordered LEAN_PATH is:

1. that toolchain's `lib/lean`;
2. host workspace `RPt_overlay`;
3. `RPz8_overlay`;
4. `RPz7_overlay`;
5. `RPz4_trusted`;
6. `RPz_trusted`.

New sources/objects reside in RPt_sources / RPt_objects. Existing S2W runner,
admission script and all predecessor objects are unchanged. RPt_inherited-pins.json
pins the RPz8 handoff, plans, verification, library classification and manifest.
RPt_inherited-object-pins.json and RPt_inherited-host-check.json record 1,663
retained paths freshly rehashed without error. These are a direct predecessor
object/sidecar recheck, not fresh compilation credit or a new full trusted-base
rebuild. The broader RPz8 trusted-base audit remains inherited evidence.

RPt_plan.json records each selected original source hash, import mapping and
root closure. All 729 snapshots differ from their selected committed inputs
only in imports (RPt_source-check.json). No original/session A/other-worker
file was edited. No alternate failed source was substituted.

## Budget and frontier

The authorized 400 attempts are fewer than the 729 new dependency vertices.
BEn was scheduled first to establish one complete root, followed by the
FJp/FJu dependency chain. Query contexts do not inflate source-closure credit.
The exact current frontier and every unbuilt vertex are RPt_frontier.json.
Fresh root audits and declaration batches are recorded separately.

BEn's 5,367 repository contexts are green (109 fresh, 5,258 reused), with an
exact checked-header closure match (RPt_BEn-import-closure-check.json).
RPt_110 checks the complete type Expr equals ARX after universe alignment,
and also checks their equality by rfl. Its full canonical kernel statement is
RPt_BEn_Top.kernel.txt: 657,311 bytes, SHA256
a0ff8eb5366d7ae62f2de7245ff482457c974da6ff9ba530d216bfd79f53ac90.
The full #print axioms and an independent checked-constant traversal both yield
only propext, Classical.choice and Quot.sound. All 180 formatter implementation
records are present and unreachable, as are all 84 actual formatter axioms.
The Formatter := Unit definition remains reachable. The retained corpus still
contains the 84 native axioms; an all-declaration standard-only claim for that
entire corpus remains false. No formatter or library implementation changed.
RPt_BEn-formatter-records.json has Boolean reachability for every record.

FJv_Top / FJv_Deployed were absent at planning; recheck at the audit stage.

## Trust, ledger and non-vacuity

RPt_LEDGER.md records the lead's accepted before/after ledger counts and
separates them from this replay's zero premise-removal delta. Complete source
statements and the pinned FJp_statement-check / FJu_statement-check evidence
are retained. Fresh kernel comparisons must be reported independently.
No changed quantifier, carrier, failure event, metric, frozen3 scope or runtime
trust item is introduced. Conditional non-vacuity is not joint deployment
inhabitation. L166 remains an external deployment-side discharge under the
owner-approved extracted-trace interpretation, with no BEn kernel binder removal.
D188 full producer/source-to-ELF provenance and remaining deployment obligations
are not established by replay.

## Resource and artifact scope

Each attempt uses one admitted systemd scope, MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64, Lean -j1 -M7000 -DElab.async=false.
Every receipt records target, command, exit, wall, peak RSS, swaps, source
revision/hash, dependency pins, cgroup limits, complete printed axioms/errors.
No Kani/Rust/SBF or shipped-file change; the ELF rebuild trigger does not fire.
Inherited release pins, not reproduced:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

No key or wallet action occurred. No binary/object/archive is committed.
