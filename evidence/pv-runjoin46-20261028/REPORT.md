# Runjoin46 — exact stored object and seven raw weight kinds

Worktree `/Users/dominic/ZK/.worktrees/pv-runjoin`, branch
`codex/pv-runjoin-20261026`, entry `841d1616f4549eb192630b50b14a0dee8c8c3e23`,
resume LOG D413. Source revision at final validation
`a943e24fb7ed56eea49d7d15d294cc06544c82e3`. IDs **61400–61499**, audit IDs
**61497–61499**. **100 Lean launches exhausted; 77 accepted / 23 rejected;
0 Kani. Target not yet established. Whole ledger rows removed: 0.**

## Checked source and model results

All 22 pending pinned weight prerequisites compiled once, in the retained order,
61400–61421. The other 64 accepted prerequisite objects were reused. The full
86-module weight prerequisite closure is now available in the pinned private
cache. No unchanged accepted module was rebuilt. Source resolution and the
prior object-reuse decision remain those recorded in runjoin45.

`PV_RunJoin_WeightCarrier46` maps the exact retained op25 representation to
`ProverCommitWeightsStorage53.State`: variant, five matrices, three points and
two extras. Named field equations and `WeightStateRoundtrip46.complete` prove
that the representation map loses no stored field. `WeightStored46.complete`
associates the constructor carrier's converted object with the explicit
`kernelState` fields.

`WeightConstructorThread46.complete` rewrites the actual constructor into its
ordered five source row calls without unfolding their arithmetic. The checked
`WeightConstructorShape46.complete` derives its actual returned fields from
those calls and the actual alpha reads, with no desired constructor success,
state or table hypothesis. `WeightBox46.complete` carries this exact object
through the actual installed op252 and every arbitrary Box request Result.
`WeightObject46.complete` binds that object, its stored fields, all seven
installed op253 raw Results, and the installed op251 **source** callback on the
same object. This source association does not install native runtime effects.

`WeightRows46.raw` proves all seven raw kinds (0–6), all Usize indices and
arbitrary stored S2 cells equal the retained `weights53.raw` Results under the
explicit scalar map. `WeightRows46.complete` transports this equation to the
actual installed op253. Kind 0 uses the checked permutation and 64-word mask
identity. Kinds 1/2/3/5/6 consume the tensor induction; kind 4 uses the shrinking
U64/U8 power induction and square/normalization transport. No desired raw
values are premises. `WeightRowArray46.complete` assembles the complete ordered
seven-value `weights53.row` Result.

`CoefficientsInstalled46.complete` proves the actual 29-column coefficient
caller with this weight dictionary installed, for arbitrary wide input cells,
with exact ordered payload and length. This preserves runjoin45's coefficient
result across the weight installation using the named op255 preservation law
and column-count induction, without reducing the full dictionary or all 29
columns together.

The scalar wrapping operations are associated separately and locally opaque.
Complex/quartic/WideExact operations, canonical reduction and WideExact-by-QM31
scaling use those named equations. Successor/absorption, point/circle/line/
doubling cells and point/circle row reference loops have complete Result laws.
`WeightCell46.complete` and `WeightFill46.complete` identify the retained model's
cell/fill with named native-arithmetic **reference folds** by induction. These
are not yet laws for the actual complete op251 materialization caller.

## Retained gaps and rejected candidates

**Step (2) remains incomplete.** `kernelState` is not yet proved to be the state
produced by `weights53.new`; the actual source statement-points computation and
row0..row4 must be identified with the model points/row constructors. The actual
materialization mutation/restoration, powers7 and allocation Result still need
to be composed with the reference fold into
`ProverCommitWeightsMaterialBinding53.run`.

The last normal attempt, 61496 (`WeightCellSource46.complete`), remains rejected
and uncredited. Its residual goals retain the row let and powers tuple/bind
structure. The accepted generic cell/fill laws do not discharge this source
bridge. `WEIGHT-NEXT.md` gives the exact consumer and next proof steps.
Both actual opening constructors, their intervening transcript/Result branches,
the 22-query append, six node multiproofs/publication indices and complete
ordered `publish_compact` proof-byte equation remain open.

The 22 rejected proof candidates and one rejected audit are retained as exact
Git blobs with verified SHA-256 in `retained-failed-sources.json`. They are not
counterexamples. Attempt 61428 hit the default recursion limit in scalar wrapper
conversion. The replacement first compiled isolated value-based wrapping
identities (61429), then rewrote through them with primitive operations locally
irreducible (61430). No failed source was rerun unchanged; no limit was raised.
Lean 4.32 local overrides use `allowUnsafeReducibility` for elaboration hints
only; kernel checking and resource limits are unchanged.
Other failures concern inference, aliases, dependent unfolding, syntax or
Result/continuation presentation. `new-source-credit-status.json` records the
current accepted sources and the single current uncredited run-46 candidate.

## Endpoint, native and deployment boundaries

Endpoint premises removed/added/weakened/changed: **0/0/0/0**. V038, V045, V163,
V165, V167 and V244 remain. No new whole-row credit is claimed for V258–V260 or
V262. The eight RunJoin fields remain exactly source_V045, E1_V329,
native_fill_V336, native_ledger_V337, byte_blind_V338, kernels_V339,
disclosed_V038 and observerOracle_V038. TrustItems remains exactly entropy_law,
entropy_kernel and observation.

The observer/simulator, coupling, bad/query events, failure/divergence
observations, public guards, failure independence, and side-channel obligations
are unchanged. Compiler cohort, deployed features/profile/ABI, D188,
allocation/TLS/filesystem, Drop/unwind and K-1/K-2 qualifications retain their
prior scope. No new native, Kani or deployed-artifact credit is claimed.
The frozen Rust/client diff from 82566acdfb is empty. Historical artifact evidence
is reused only in that unchanged scope.

No shipped source, key/account, protected soundness file, root checkout, other
worktree or shared source/cache was changed. No push, merge, extraction, ELF
rebuild, native differential or unchanged full regression ran. `step3-merge-check.json`
finds no merge of `codex/pv-rjdec-20261028`; its branch/prefix and step (3) were
untouched. Step (4) was not started.

## Validation and admission

Initial preflight: 2850 project pairs, 6008 direct fingerprints, 5673 external
objects and 5438 IR companions. Final preflight: **2927 project pairs, 6159
direct fingerprints, 5673 external objects and 5438 IR companions**, all
matching. Full preflights are compressed with uncompressed SHA-256 sidecars.
The pinned runjoin32-lean workspace and toolchain are reused (Lean 4.32.0,
commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35).

Every launch used one module in one scope, MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64 and Lean -M7000. Admission ran in the same shell
command as the scope, requiring exit 0 and explicit allowed:true. All **100**
launches pass `admission-launch-audit.json`: zero void launches, zero cooldown
violations. **Eight** refusals launched no compiler, were uncharged and reused
the same ID after the full 180-second cooldown. No scan race or memory kill
occurred. Scope intervals are disjoint; final own running scopes: zero.

The first reserved audit, 61497, failed because its round-trip query lacked an
import. Its four other queries printed standard axioms, but that failed audit
is not credited. The changed source adds the missing import and passes at 61498.
61499 combines the coefficient and source/model audits; the two unused draft
audit files were superseded. No theorem from rejected 61496 is imported.

| ID | Exact audit target | Exit | Wall s | Peak RSS bytes | Swap |
| --- | --- | --- | --- | --- | --- |
| 61497 | R1Z.PV_RunJoin_WeightAudit46 | 1 | 2.05 | 4424921088 | 0 |
| 61498 | R1Z.PV_RunJoin_WeightAudit46 | 0 | 1.83 | 4433526784 | 0 |
| 61499 | R1Z.PV_RunJoin_CombinedAudit46 | 0 | 1.84 | 4456615936 | 0 |

All accepted printed axiom sets are subsets of propext, Classical.choice and
Quot.sound. Peak RSS over all attempts was **4475080704 bytes**; every swap
count was zero. Per-attempt receipts contain exact source revisions/blobs/hashes,
dependency fingerprints, commands, status, wall, RSS, swap and original axiom
output. `original-module-logs.json.xz` hash-verifies all 100 original output/time
pairs. These are focused checks, not a frozen-manifest release replay.

Stopped on the **100-attempt Lean budget**, not on a checked counterexample or
reservation refusal. The next deliverable is the actual source cell/outer-loop
and stored-constructor model association described in `WEIGHT-NEXT.md`, followed
by the complete opening-constructor composition. `commits.txt` records commits
since entry; an evidence-only freeze commit follows its generation.
