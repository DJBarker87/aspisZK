# Release trust audit — 26 October 2026

**L188 first pass: findings, not a release-gate pass. Target not yet established.**
Targets: `AspisR1.FGl_Headline.deployed` and `AspisR1.Rc6_Top.deployed`.
Branch: `codex/cx-trust-audit-20261026`. Sources and theorem statements are unchanged.
Receipts and exact executed query modules: [TAu evidence](../evidence/trust-audit-20261026/).
No proof, Kani harness, shipped source, candidate, dictionary or ELF was changed.

## Result and limits

Fresh `#check` and `#print axioms` of both actual top theorems passed in
[TAu_001](../evidence/trust-audit-20261026/TAu_001/stdout.log).
Both report exactly `[propext, Classical.choice, Quot.sound]`. The same query
also checks `FGl_Nonvacuity.composed`, with those same axioms. These are results
on the selected imported objects, not a new coherent release replay.

The broader audit observed **67 distinct nonstandard axiom names** in imported
query results. Every name is listed below and machine-indexed with its exact
queried declaration and attempt in
[TAu_kernel-results.json](../evidence/trust-audit-20261026/TAu_kernel-results.json).
The three permitted standard axioms are also present. No nonstandard name
appears in either top theorem's printed axiom list. Import membership and
proof dependence must not be conflated.

Coverage is explicitly incomplete: the selected metadata/source graph has
10,389 modules; one representative declaration was planned for 9,564 modules,
and 9,488 modules have a matching successful printed result. 825 modules have
no available named declaration in the reused census/source scan; another 76
lack a matching result. This is **not** an exhaustive audit of every declaration.
The scanner reused the raw import-union census, hash-matched object manifests,
and selected sources; it did not decode every selected object afresh. Four
selected circle-module import headers remain unavailable. Their exact names,
object hashes and all coverage gaps are in
[TAu_closure.json](../evidence/trust-audit-20261026/TAu_closure.json) and
[TAu_module-coverage.json](../evidence/trust-audit-20261026/TAu_module-coverage.json).
Source-only edges are weaker evidence than hash-matched object headers.

**Budget exhausted: 30/30 Lean invocations, 0/0 Kani.** Thirteen invocations
exit 0; seventeen contain diagnostic query errors. All compiler output is
retained, including useful results preceding/following errors. There are 41
error diagnostics, including quoted syntax-name spelling failures, inaccessible
generated/private names, and three obsolete generated axiom names. TAu_030
repaired several earlier query spellings; it still contains one unresolved
syntax declaration name. A failed invocation is never described as a passing
module audit. No timeout, memory kill or cap increase occurred. No further
Lean invocation is authorized by this job's budget.

## Axiom and provenance findings

**A1 — nonstandard imported dependencies.** Formatter reaches the SOUNDNESS
*import graph* and is reported by, among others,
`Aeneas.Std.core.fmt.num.imp.DisplayU8.fmt.eq_1` (TAu_004),
`Aeneas.Std.DiscriminantKind.mk.inj` (TAu_021),
`Aeneas.Std.core.error.Error.mk.inj` (TAu_023), and
`Aeneas.Std.core.array.DebugArray.fmt.eq_1` (TAu_024).
It does **not** occur in either top theorem's reported dependencies.
Aeneas test axioms, opaque library types/environment contracts, compiler/native
reduction declarations, and generated public-preparation Debug native-decision
axioms are also findings under the requested closure-wide standard-only rule.
The occurrence of `sorryAx` in the full list is the query of `sorryAx` itself;
no audited security theorem was observed to depend on it. Merely importing
Init, which declares it, is not a proof containing `sorry`.

**A2 — stored axiom-summary discrepancy.** In the SAME audit environment,
`#print axioms Aeneas.Std.core.fmt.Formatter` reports no axioms (TAu_004), while
the imported declarations above report Formatter. The selected Fmt object is
SHA256 `63b8efa3940faa81bb26f1b6ea140b2d6b81c1f1155b3fafa0544f6e1e82b9fc`;
Core.Error is `666269a61518620f1b9f7e1c190e42ccbf83f982c5015d8303dda2b7d51f927d`.
These are separately pinned in the SInt2 object manifest; Fmt differs from the
historical raw census, whereas Core.Error matches that census. The pinned
Lean 4.32 implementation looks up imported declarations' precomputed axiom
summaries rather than recursively walking their imported bodies; see
[the inspected implementation](../evidence/trust-audit-20261026/TAu_collectAxioms-source.txt).
This explains why a historical summary can survive a changed dependency;
it does not prove which summaries need replacement. Treat this as a cache
provenance finding requiring L187's coherent replay, rather than silently
removing Formatter from the list or claiming that the current headlines
transitively use it. The observed standard-only headline summaries remain
recorded faithfully; independent recomputation of all bodies was not done.

**A3 — external templates.** No selected module name ends in
`FunsExternal_Template`. Selected `FunsExternal` modules include
`AspisR1AdapterReconstruct`, `AspisR1TerminalDecoder`,
`AspisR1WideToBytesSource` and `WAdm_Fissioned`. The first two census inventories
contain only concrete discriminant helpers; the last is a concrete owned
iterator interpretation. No template axiom reaches either headline's
reported dependency set. This does not certify every external module: the
wide-to-bytes external modules lack a declaration census in this pass, and
the broader coverage/provenance limitations above remain. Unimported raw
extraction templates are source-generation artifacts, not adopted axioms.

**A4 — closure audit incomplete.** Missing import headers and unqueried
modules/declarations prevent an exhaustive release-wide axiom inventory.
Do not close L188 from two clean headline summaries or from the 67-name list.
Resolve A2 with a coherent, capped replay, then audit the complete selected
object environment, including modules with no representative in this pass.
No infrastructure, source dependency or shared object was repaired here.

## Release trust table

The exact full kernel statements of all fifteen SDK fields, both entry
records, extraction, copy, syscall, persistence and game are in
[TAu_002/stdout.log](../evidence/trust-audit-20261026/TAu_002/stdout.log).
Additional library/configuration/allocator-dictionary statements are in
[TAu_030/stdout.log](../evidence/trust-audit-20261026/TAu_030/stdout.log).
The table's formulas abbreviate those printed statements without changing
their quantifiers. “Accepted” describes scope authorization, not a concrete
implementation proof or joint inhabitation of all premises.

Acceptance sources:
[contract and owner amendment](../docs/research/100bit-spend-path-20261013/design/SECURITY-CONTRACT-20261021.md#owner-approved-amendment-2026-10-26),
[C3-BIN](../docs/research/100bit-spend-path-20261013/design/C3-BIN-20261021.md),
[LOG](../docs/research/v8-r0-zk-20261009/LOG.md).
Dates/titles below disambiguate duplicate LOG numbers.

| Item / current location | Exact statement reference and scope | Acceptance citation | Width / status |
|---|---|---|---|
| `S2Trust.S2TrustedSdkBorrow L`; `sdk` in both tops; L001–034 | TAu_002 prints all 15 fields: `account_data_cell`, `cell_payload`, `cell_counter`, `shared_ok`, `shared_err`, `exclusive_ok`, `exclusive_err`, `shared_deref`, `exclusive_deref`, `guard_move`, `shared_drop`, `exclusive_drop`, `error_move_drop`, `borrow_frame`, `guard_liveness`. Each operation law is guarded by `L.related w s` and `Valid s`, plus the operation's enabled/counter/lifetime conditions. `Matches` relates reply AND next heap. | C3-BIN **2026-10-23 01:20**, “S2 diagnosis and route B adopted”, D177; LOG D189, **2026-10-23 17:35** | Same fifteen-field route B; no observed added field. Pinned SDK 2.3.0 / production lock. Does not authorize Ref clone/map_split/leak, realloc, Rc clone/free, lamport borrows, CPI, concurrency or reentrancy. Actual carrier association belongs here, but caller/source laws do not. |
| `S2W_TrustedStd.TrustedStd copy`; `std`; L035 | `slice_copy_from_slice : ∀ s dst src, copy s dst src = specification s dst src`. `specification` returns `copyHeap` exactly when descriptor lengths agree, otherwise `.panic`; `copyHeap` changes only destination payload contents. Exact definitions: TAu_002. | LOG D157, **2026-10-22 08:35**; C3-BIN **2026-10-23 18:05** explicitly names copy_from_slice; D133/D145/D156 are the earlier policy precedents | **W1 domain finding:** the printed formula quantifies all abstract heaps/payloads, while the documented native interpretation is on valid exclusive/shared references. It lacks a validity/admission guard. It can be a total abstract extension, but no acceptance of native invalid-reference semantics was found. The association must justify using only admitted states, or a later proof must restrict this hypothesis. No new trust is approved here. |
| `Port1_Library.TrustedStd`; deployment L192–193 | `option_ok_or : ∀ {T E} x e, ops.op0 x e = Port1_LibrarySource.okOr x e`; `result_unwrap32 : ∀ x, ops.unwrap32 x = Port1_LibrarySource.unwrap32 x`. TAu_030. | LOG D157; C3-BIN **2026-10-23 18:05** and **2026-10-25 late**, trust separation | Pure Option/Result semantics; no observed widening. Not a new hidden top-level copy field. Concrete installed operations and value lemmas do not establish native frame/ownership/effects (L179/L186). |
| `S2W_DigestExtraction.AeneasExtraction ops native1 native2 hashv`; `extraction`; L078–080 | `stage1 : ∀ program accounts data, native1 program accounts data = AdapterRw.r1_pool_adapter.owned.stage1_owned ops program accounts data`; analogous `stage2` with `slot`; `digestSource : ∀ self parts, ops.op43 self parts = S2W_DigestExtraction.digest hashv self parts`. TAu_002. | LOG D188 **2026-10-23 16:40**, D189 **17:35**; C3-BIN **18:05**; **2026-10-26 native Vec/Box ruling** | Within accepted extracted-source association, not SBF equivalence. Safe extracted Vec/Box uses Aeneas's model. Unsafe MaybeUninit/uninit/raw writes still require the P6 safe-reference route. No conclusion/account/frame/site/oracle-log field is licensed by extraction alone. |
| P6 / Kani association; deployment L190 | **No named Lean P6/Kani hypothesis in either printed top.** External acceptance of exact shipped/reference Kani Result/effects/content correspondence, then reference extraction. It is distinct from `MultiproofConeP6Frozen2Stage.P6Boundary`, whose exact source callback/oracle fields are printed in TAu_030 and are an output of these tops. | C3-BIN **2026-10-23 02:40**, owned-reference/Kani route; LOG D188; C3-BIN **2026-10-25 late** §4; **2026-10-26 native Vec/Box ruling (b)** | Accepted tool association, not permission to assert an arbitrary source refinement. Unsafe construction/native effect association remains P. Do not turn returned `P6Boundary` into proof that Kani covered the deployed batch. |
| `S2W_D189Wrappers.Allocator A`; `allocator`; deployment L191 alias | Data interface: `allocate : A → Nat → Result A`, `cleanup : A → Result A`. TAu_002. No Prop field guaranteeing success, totality or account access. | C3-BIN **2026-10-23 02:40**, OOM/runtime rollback; **11:05 / 18:05**, P2–P4/private runtime region; **2026-10-26 native Vec/Box ruling (c)** | No observed widening. Account separation is expressed by the private-state model/signatures, not an allocator permission to mutate account buffers. Actual-runtime association remains separate. |
| `S2W_D189Consolidation.RuntimeEntrypointAdmission L e w n`; `admission1/2`; L036–077 | `entry : AdapterRw.RuntimeEntrypointAdmission e.heap keys n`; `related : L.related w e.heap`. Nested entry fields: `Valid`, fresh guards, no external borrows, live accounts, zero counters, alias implies equal keys and equal keys imply shared cells. Exact TAu_002. | C3-BIN **2026-10-23 02:40 / 18:05**; LOG D189 for typed-carrier relation | Initial admissibility only; no acceptance, post-state, allocator success, CPI or persistence claim. No observed widening; n is 3/7 at the two actual calls. |
| `S2W_ExtractionBoundary.P1 sha256 H`; `p1`; L081 | `realization : S2Z.Oracle.P1Realization sha256 H`, definition `∀ bytes, sha256 bytes = H bytes`. TAu_002. | Existing P1; C3-BIN **2026-10-23 11:05 / 18:05** | Explicit ideal-oracle realization boundary; not a Lean theorem that real SHA is random. No observed widening or new cryptographic assumption introduced by this audit. |
| `S2W_ExtractionBoundary.RuntimeSyscall hashv sha256`; `syscall`; L082 | `returningValue : ∀ parts digest, hashv parts = ok digest → decodeState digest = sha256 (flatten parts)`. TAu_002. | C3-BIN **2026-10-23 11:05 / 18:05**; P3 | Success-conditioned, allows failure/divergence. No observed widening. Multiproof totality cannot be assumed from this field. |
| `S2X.CheckpointVersionBinding saved loaded`; historical interface, **not a free argument of these tops** | `key`, `ledger`, `events`, `savedAtCommit : ledger key = saved`, `loadedAtEntry : loaded = history ledger events key`, `noInterveningWrite : ∀ event ∈ events, Preserves key event`. TAu_002. | C3-BIN **2026-10-23 11:05 / 18:05**; current owner amendment **2026-10-26** supplies the narrower data runtime item and game | Old conditional history interface. Do not count it as an additional adopted top-level runtime hypothesis or assume it discharged merely because wrapped. Current history chain derives what it needs from the selected game/runtime/source records; no new widened checkpoint authority is approved. |
| `CPR_DataPersistence.TwoTransactionLaw`; `RuntimePersistence`; Rc5_T001 | `∀ t u, next t u → ∀ key, ordinary t key → loaded u key = visible (if success t then tentative t key else before t key)`, `visible image = if image.lamports = 0 then none else some image.data`. Exact instantiated selectors in TAu_001/002. | Contract **Owner-approved amendment, 2026-10-26 §3**; `design/RUNTIME-PERSISTENCE-ITEM-20261026.md` | Accepted data-only law. No owner/privilege/balance equality, no SDK/verifier promise. Ordinary excludes fee payer and durable nonce; bank adjacency is selected separately. No observed widening to full account images. |
| P7 compiler/LLVM/platform tools; L189, applied through L186 | **No named Lean P7/toolchain hypothesis in either printed top.** Deployment claim: pinned source/features/ABI/toolchain lowering preserves the selected source semantics for the three exact ELFs. L186 is the concrete association obligation; P7 is the trusted compiler boundary. | Existing P1–P7 contract; C3-BIN **2026-10-25 late** §4; LOG D188 separates extraction from binary correspondence | Accepted tool trust, not source-to-ELF proof. Source hash reproduction alone is not semantic lowering; L186 remains P. No observed authorization to widen to arbitrary source/features/toolchains. |
| Security assumptions/model; L194 | Both statements' exact frozen3 source/runtime/probability conclusions and query bounds: TAu_001. These are not extra global `axiom` declarations. | Security contract, including **2026-10-26 amendment §1**: frozen3, charged collision branch, unchanged 100-bit metric/constants | No target/metric/adversary change by this audit. Query-budget, source/model/runtime transport and arithmetic rows remain P. Numeric model bounds alone are not unconditional deployed security. |
| Game a–d and wrapper acceptance; **G, not external trust** | Exact `CPH_Game.DeployedPairExecution` fields in TAu_002; exact `accepted1/accepted2` equalities in TAu_001; expansion and classification below | Owner amendment **2026-10-26 §2(a–d)**; C3-BIN **2026-10-23 18:05**, “acceptance of both wrappers (success conditioning)” | Approved experiment definition. No extra attacker restriction or persistence law is silently inferred. Conditional non-vacuity remains a separate verification concern. |

The 83 actual T rows expand as 34 SDK + 1 copy + 42 entry-admission + 3 extraction
+ 1 P1 + 1 syscall + 1 RuntimePersistence. Six deployment-only T rows are
L189–194. Allocator is a data interface, not an extra successful-allocation
axiom; aliases do not create extra independent trust rows.

`Configuration.std : ClaimsUnrolledFinish.StdCalls` and
`reservation : NP6_StdModel.Reservation` are operation/data carriers, not
propositions that the unsafe shipped Claims buffers have the safe owned
semantics. The native Vec/Box ruling explicitly preserves that P6 obligation.
The exact dictionaries are printed in TAu_030. There is no silent promotion
of `reserve`/`intoBox` fields to an accepted unsafe-memory trust item.

## Acceptance-log scope check

LOG D133 (2026-10-21), D145 (2026-10-22 03:45), and D156 (08:15) authorize
ordered-map/set documented semantics in the **prover** trust cone. They are
policy precedents for route B, not extra soundness hypotheses in these tops.
D157 (08:35) permits named pure std collection/slice semantics and explicitly
excludes I/O, allocation failure, concurrency, interior mutability, HashMap
ordering and unsafe code. Route B therefore needs, and has, its separate
01:20 ruling. D178 (2026-10-23 02:50) accepts the import-union migration and
records old Formatter exceptions; it is not blanket acceptance of opaque
axioms. D188/D189 have the narrower extracted-source/carrier meanings above.

LOG has two D192 headings: **2026-10-24, “explicit entropy preflight reviewed;
cap16 source gate next”** retains E1/E2/native association and authorizes no
new trust; **2026-10-26, “host barrier cap correction for the prover candidate”**
is a resource correction, not semantics acceptance. Neither authorizes an
Aeneas external template or unsafe source law in the soundness theorem.
No entropy/prover trust item is smuggled into the soundness list from either.

## G classification: approved experiment, not must-prove refinement

Propose ledger class **G = definition/conditioning of the owner-approved
experiment**. Keep its clauses visible; do not erase them from the theorem,
move them into T, or assert they prove a concrete runtime instance. The
acceptance citation is the contract's 2026-10-26 amendment §2(a–d), together
with C3-BIN 2026-10-23 18:05's explicit successful-wrapper conditioning.

| Ledger row | Actual current clause | Contract clause | Class |
|---|---|---|---|
| Rc5_G001 | `game.consecutive.1 : p.next t u` | (a), consecutive bank-lineage executions | G |
| Rc5_G002 | `game.consecutive.2.1 : e1 = CPG_Projection.entry p t` | (a), TX1 entry of that execution | G |
| Rc5_G003 | `game.consecutive.2.2 : e2 = CPG_Projection.entry p u` | (a), TX2 entry of that execution | G |
| Rc5_G004 | `game.checkpoint.1 : ((p.layout t).handles 2).1 = ((p.layout u).handles 6).1` | (b), same bank account key | G |
| Rc5_G005 | `game.checkpoint.2.1 : CPS_PhysicalKey.key e1 2 = CPS_PhysicalKey.key e2 6` | (b), same physical CP public key | G |
| Rc5_G006 | `game.checkpoint.2.2 : ((p.layout t).handles 2).1 ∉ p.intervening t u` | (b), no intervening touch | G |
| Rc5_G007 | `game.parent : CPG_Projection.success p t = true` | (c), final parent success | G |
| Rc5_G008 | `game.recorded.1.1 : p.copied t = saved` | (d), actual checkpoint copy | G |
| Rc5_G009 | `game.recorded.1.2.1 : p.actions t = actions` | (d), actual action list | G |
| Rc5_G010 | `game.recorded.1.2.2 : CPG_RuntimeTrace.Executes ...` starting at `CPR_SourceBank.afterCopy ... saved` | (d), physical TX1 suffix execution; full exact type in TAu_002 | G |
| Rc5_G011 | `game.recorded.2 : CPG_RuntimeTrace.Executes ...` starting at `cached (p.bank u)` | (d), physical TX2 execution; full exact type in TAu_002 | G |
| L083 | `S2W_D189Wrappers.first native1 copy allocator e1 CPH_Program.verifier data1 state1 = ok (.Ok (saved,post1,final1))` | successful TX1 in the two-transaction spend; existing success-conditioned theorem | G |
| L084 | `S2W_D189Wrappers.second native2 allocator e2 CPH_Program.verifier data2 slot state2 = ok (.Ok (post2,final2))` | successful TX2/accepted failure event; existing success-conditioned theorem | G |

This classification does not permit deleting rejected oracle prefixes from the
security experiment. Those prefixes remain in the source/runtime carrier and
query-budget obligations. Nor does it prove that a chosen concrete execution
inhabits G. JFz_ is the concurrent joint-fixture job; no result from its branch
was read, imported or credited here.

## Before/after statements, recount and non-vacuity

The before and after theorem statements are **identical**. Full kernel text:
[FGl before](../evidence/trust-audit-20261026/TAu_FGl_Headline_BEFORE.lean.txt),
[FGl after](../evidence/trust-audit-20261026/TAu_FGl_Headline_AFTER.lean.txt),
[Rc6 before](../evidence/trust-audit-20261026/TAu_Rc6_Top_BEFORE.lean.txt),
[Rc6 after](../evidence/trust-audit-20261026/TAu_Rc6_Top_AFTER.lean.txt).
The original source modules were neither edited nor recompiled.

| Scope | Existing T/P | Proposed T/P/G | Accounting delta |
|---|---:|---:|---|
| FGl actual | 83/41 | 83/28/13 | 13 P→G; no theorem premise removed |
| FGl actual + non-alias deployment | 89/49 | 89/36/13 | same reclassification; L188 retained |
| Rc6 actual | 83/32 | 83/19/13 | same reclassification |
| Rc6 actual + non-alias deployment | 89/40 | 89/27/13 | same reclassification |

Recount method: preserve every existing law-family row, original domain and
alias status; change only the thirteen listed classifications. Do not merge
native-local arithmetic with FGl's world-global arithmetic. Do not double-count
L182/L185 deployment aliases. No T or C row is removed/added. No logical premise,
quantifier, carrier, acceptance guard, failure event or conclusion changes.
The mechanical script and exact row-by-row output are
[TAu_recount.py](../evidence/trust-audit-20261026/TAu_recount.py) and
[TAu_recount.json](../evidence/trust-audit-20261026/TAu_recount.json).
This audit has **zero premise-removal credit** under the owner's completion rule.

Non-vacuity: the fresh TAu_001 check/audit of `FGl_Nonvacuity.composed` reuses
its previously checked conditional theorem. It applies the actual FGl headline
to the same native accepted cuts and obtains an accepted source/runtime run
and positive zero-query margin, under its retained boundary/owner hypotheses.
No joint inhabitation of every release premise is established by this check.
G reclassification adds no condition and removes none; it cannot make a formerly
vacuous deployment inhabited. The current domain/cost/game qualifications of
FGl versus Rc6 remain exactly as disclosed in the FGl handoff.

## Remaining P rows and coverage

The following tables exhaust the proposed P rows, including explicitly marked
aliases. Job labels describe responsibility or proposed coverage, **not merged
proofs**. BEf_ is the documented batch-effects assignment. P2P_, SCE_ and FIn_
are plausible corresponding concurrent work streams and are marked proposed
where this checkout contains no authoritative assignment/result. Session A's
arithmetic ownership is retained; its candidates/worktrees were not touched.
JFz_ covers joint-fixture/non-vacuity validation rather than universal removal
of a remaining P family. Unassigned release gates are marked uncovered.

### FGl remaining P inventory

| ID | Scope | Family | Covering job / unresolved owner |
|---|---|---|---|
|L097|actual antecedent|p2prime.binding.proof|P2P_ (proposed); JFz_ fixture only|
|L098|actual antecedent|p2prime.binding.pub|P2P_ (proposed); JFz_ fixture only|
|L133|actual antecedent|pairing_S3_S5_S9.round0.boundary|session A (SAG_ in baseline); FIn_ integration proposed|
|L134|actual antecedent|pairing_S3_S5_S9.round0.quarter|session A (SAG_ in baseline); FIn_ integration proposed|
|L135|actual antecedent|pairing_S3_S5_S9.round0.eval|session A (SAG_ in baseline); FIn_ integration proposed|
|L136|actual antecedent|pairing_S3_S5_S9.round1.boundary|session A (SAG_ in baseline); FIn_ integration proposed|
|L137|actual antecedent|pairing_S3_S5_S9.round1.quarter|session A (SAG_ in baseline); FIn_ integration proposed|
|L138|actual antecedent|pairing_S3_S5_S9.round1.eval|session A (SAG_ in baseline); FIn_ integration proposed|
|L142|actual antecedent|pairing_S3_S5_S9.pair|session A (SAG_ in baseline); FIn_ integration proposed|
|L143|actual antecedent|matches_S4_S7|session A (SAG_ in baseline); FIn_ integration proposed|
|L144|actual antecedent|semantic_S3_S9.EquationEndpoint.initial|session A (SAG_ in baseline); FIn_ integration proposed|
|L145|actual antecedent|semantic_S3_S9.EquationEndpoint.chain|session A (SAG_ in baseline); FIn_ integration proposed|
|L146|actual antecedent|semantic_S3_S9.EquationEndpoint.terminal|session A (SAG_ in baseline); FIn_ integration proposed|
|L147|actual antecedent|dot_S5|session A (SAG_ in baseline); FIn_ integration proposed|
|L154|actual antecedent|hqueries|UNCOVERED resource/query association|
|L159|actual antecedent|frozen3 StoredCarrierBinding|SCE_ (proposed); L157 Rc6 only|
|L165|deployment only|shape full semantic/transcript join|SCE_ (proposed); L157 Rc6 only|
|L166|deployment only|batch source Result/effects|BEf_|
|L176|deployment only|S6 native decoded/public transport|session A S6; native transport UNCOVERED|
|L179|deployment only|library/native frame|UNCOVERED native library frame; safe-reference predecessor only|
|L181|deployment only|oracle model order|SCE_ (proposed); L157 Rc6 only|
|L185|deployment alias|deployed stored experiment|SCE_ (proposed); L157 Rc6 only|
|L186|deployment only|source lowering to frozen ELFs|UNCOVERED release lowering/lead|
|L187|deployment only|coherent frozen replay|UNCOVERED coherent final replay/lead|
|L188|deployment only|final axioms/trust audit|TAu_ first pass; findings remain OPEN|
|F3Y_G_L133|actual antecedent|finishOwners.source_global.pairing_S3_S5_S9.round0.boundary|session A arithmetic; FIn_ integration proposed|
|F3Y_G_L134|actual antecedent|finishOwners.source_global.pairing_S3_S5_S9.round0.quarter|session A arithmetic; FIn_ integration proposed|
|F3Y_G_L135|actual antecedent|finishOwners.source_global.pairing_S3_S5_S9.round0.eval|session A arithmetic; FIn_ integration proposed|
|F3Y_G_L136|actual antecedent|finishOwners.source_global.pairing_S3_S5_S9.round1.boundary|session A arithmetic; FIn_ integration proposed|
|F3Y_G_L137|actual antecedent|finishOwners.source_global.pairing_S3_S5_S9.round1.quarter|session A arithmetic; FIn_ integration proposed|
|F3Y_G_L138|actual antecedent|finishOwners.source_global.pairing_S3_S5_S9.round1.eval|session A arithmetic; FIn_ integration proposed|
|F3Y_G_L142|actual antecedent|finishOwners.source_global.pairing_S3_S5_S9.pair|session A arithmetic; FIn_ integration proposed|
|F3Y_G_L143|actual antecedent|finishOwners.source_global.matches_S4_S7|session A arithmetic; FIn_ integration proposed|
|F3Y_G_L144|actual antecedent|finishOwners.source_global.semantic_S3_S9.EquationEndpoint.initial|session A arithmetic; FIn_ integration proposed|
|F3Y_G_L145|actual antecedent|finishOwners.source_global.semantic_S3_S9.EquationEndpoint.chain|session A arithmetic; FIn_ integration proposed|
|F3Y_G_L146|actual antecedent|finishOwners.source_global.semantic_S3_S9.EquationEndpoint.terminal|session A arithmetic; FIn_ integration proposed|
|F3Y_G_L147|actual antecedent|finishOwners.source_global.dot_S5|session A arithmetic; FIn_ integration proposed|

### Rc6 remaining P inventory

| ID | Scope | Family | Covering job / unresolved owner |
|---|---|---|---|
|L097|actual antecedent|p2prime.binding.proof|P2P_ (proposed); JFz_ fixture only|
|L098|actual antecedent|p2prime.binding.pub|P2P_ (proposed); JFz_ fixture only|
|L133|actual antecedent|pairing_S3_S5_S9.round0.boundary|session A (SAG_ in baseline); FIn_ integration proposed|
|L134|actual antecedent|pairing_S3_S5_S9.round0.quarter|session A (SAG_ in baseline); FIn_ integration proposed|
|L135|actual antecedent|pairing_S3_S5_S9.round0.eval|session A (SAG_ in baseline); FIn_ integration proposed|
|L136|actual antecedent|pairing_S3_S5_S9.round1.boundary|session A (SAG_ in baseline); FIn_ integration proposed|
|L137|actual antecedent|pairing_S3_S5_S9.round1.quarter|session A (SAG_ in baseline); FIn_ integration proposed|
|L138|actual antecedent|pairing_S3_S5_S9.round1.eval|session A (SAG_ in baseline); FIn_ integration proposed|
|L142|actual antecedent|pairing_S3_S5_S9.pair|session A (SAG_ in baseline); FIn_ integration proposed|
|L143|actual antecedent|matches_S4_S7|session A (SAG_ in baseline); FIn_ integration proposed|
|L144|actual antecedent|semantic_S3_S9.EquationEndpoint.initial|session A (SAG_ in baseline); FIn_ integration proposed|
|L145|actual antecedent|semantic_S3_S9.EquationEndpoint.chain|session A (SAG_ in baseline); FIn_ integration proposed|
|L146|actual antecedent|semantic_S3_S9.EquationEndpoint.terminal|session A (SAG_ in baseline); FIn_ integration proposed|
|L147|actual antecedent|dot_S5|session A (SAG_ in baseline); FIn_ integration proposed|
|L154|actual antecedent|hqueries|UNCOVERED resource/query association|
|L157|actual antecedent|frozen3 canonicalJoin.verifier|SCE_ (proposed); L157 Rc6 only|
|L159|actual antecedent|frozen3 StoredCarrierBinding|SCE_ (proposed); L157 Rc6 only|
|N117|actual antecedent|prefixBound|UNCOVERED resource/query association|
|N118|actual antecedent|choiceBound|UNCOVERED resource/query association|
|L165|deployment only|shape full semantic/transcript join|SCE_ (proposed); L157 Rc6 only|
|L166|deployment only|batch source Result/effects|BEf_|
|L176|deployment only|S6 native decoded/public transport|session A S6; native transport UNCOVERED|
|L179|deployment only|library/native frame|UNCOVERED native library frame; safe-reference predecessor only|
|L181|deployment only|oracle model order|SCE_ (proposed); L157 Rc6 only|
|L182|deployment alias|raw canonical join|SCE_ (proposed); L157 Rc6 only|
|L185|deployment alias|deployed stored experiment|SCE_ (proposed); L157 Rc6 only|
|L186|deployment only|source lowering to frozen ELFs|UNCOVERED release lowering/lead|
|L187|deployment only|coherent frozen replay|UNCOVERED coherent final replay/lead|
|L188|deployment only|final axioms/trust audit|TAu_ first pass; findings remain OPEN|

## Complete observed axiom-name list

Standard permitted names: `propext`, `Classical.choice`, `Quot.sound`.

All 67 additional names returned by the queries follow. These are **observed axiom dependencies**, not a certification that each name is currently an axiom declaration: A2 demonstrates why that distinction matters. Exact witnesses/attempts are in TAu_kernel-results.json. Some names are unsafe runtime/compiler declarations or generated test/debug facts, not assumptions of either security theorem. They nevertheless remain findings under the requested import-wide rule.

```text
Aeneas.Command.Decompose.TestsRec.recAxOp
Aeneas.Std.core.fmt.Formatter
Aeneas.Std.core.panic.panic_info.PanicInfo
Aeneas.Std.core.pin.Pin
Aeneas.Std.core.pin.helper.PinHelper
Aeneas.Std.core.sync.atomic.AtomicBool
Aeneas.Std.core.sync.atomic.AtomicU32
Aeneas.Std.get_target
Aeneas.Std.get_target.spec
Aeneas.StepArraySpec.Tests.const_array_spec._native.native_decide.ax_1_1
AspisR1PublicPreparation.aspis_core.field.M31.Insts.CoreFmtDebug.fmt._native.decide.ax_1
AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1.Insts.CoreFmtDebug.fmt._native.decide.ax_1
AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1.Insts.CoreFmtDebug.fmt._native.decide.ax_2
AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1.Insts.CoreFmtDebug.fmt._native.decide.ax_3
AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1.Insts.CoreFmtDebug.fmt._native.decide.ax_4
AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1.Insts.CoreFmtDebug.fmt._native.decide.ax_5
AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1.Insts.CoreFmtDebug.fmt._native.decide.ax_6
AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1.Insts.CoreFmtDebug.fmt._native.decide.ax_7
AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1.Insts.CoreFmtDebug.fmt._native.decide.ax_8
AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.Insts.CoreFmtDebug.fmt._native.decide.ax_3
AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.Insts.CoreFmtDebug.fmt._native.decide.ax_4
AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.Insts.CoreFmtDebug.fmt._native.decide.ax_5
AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.Insts.CoreFmtDebug.fmt._native.decide.ax_6
AspisR1PublicPreparation.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1.Insts.CoreFmtDebug.fmt._native.decide.ax_1
AspisR1PublicPreparation.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1.Insts.CoreFmtDebug.fmt._native.decide.ax_2
AspisR1PublicPreparation.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1.Insts.CoreFmtDebug.fmt._native.decide.ax_3
AspisR1PublicPreparation.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1.Insts.CoreFmtDebug.fmt._native.decide.ax_4
AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreFmtDebug.fmt._native.decide.ax_1
AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreFmtDebug.fmt._native.decide.ax_2
AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreFmtDebug.fmt._native.decide.ax_3
AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1.Insts.CoreFmtDebug.fmt._native.decide.ax_1
AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1.Insts.CoreFmtDebug.fmt._native.decide.ax_2
AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1.Insts.CoreFmtDebug.fmt._native.decide.ax_3
AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1.Insts.CoreFmtDebug.fmt._native.decide.ax_4
AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1.Insts.CoreFmtDebug.fmt._native.decide.ax_5
AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1.Insts.CoreFmtDebug.fmt._native.decide.ax_6
AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1.Insts.CoreFmtDebug.fmt._native.decide.ax_1
AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1.Insts.CoreFmtDebug.fmt._native.decide.ax_2
AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1.Insts.CoreFmtDebug.fmt._native.decide.ax_3
AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1.Insts.CoreFmtDebug.fmt._native.decide.ax_4
AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1.Insts.CoreFmtDebug.fmt._native.decide.ax_5
AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1.Insts.CoreFmtDebug.fmt._native.decide.ax_6
AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1.Insts.CoreFmtDebug.fmt._native.decide.ax_7
AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1.Insts.CoreFmtDebug.fmt._native.decide.ax_8
AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1.Insts.CoreFmtDebug.fmt._native.decide.ax_9
AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1.Insts.CoreFmtDebug.fmt._native.decide.ax_1
AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1.Insts.CoreFmtDebug.fmt._native.decide.ax_10
AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1.Insts.CoreFmtDebug.fmt._native.decide.ax_2
AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1.Insts.CoreFmtDebug.fmt._native.decide.ax_3
AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1.Insts.CoreFmtDebug.fmt._native.decide.ax_4
AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1.Insts.CoreFmtDebug.fmt._native.decide.ax_5
AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1.Insts.CoreFmtDebug.fmt._native.decide.ax_6
AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1.Insts.CoreFmtDebug.fmt._native.decide.ax_7
AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1.Insts.CoreFmtDebug.fmt._native.decide.ax_8
AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1.Insts.CoreFmtDebug.fmt._native.decide.ax_9
Lean.ofReduceBool
Lean.ofReduceNat
Lean.trustCompiler
Quot.lcInv
isScalarObj
lcAny
lcCast
lcErased
lcProof
lcUnreachable
lcVoid
sorryAx
```

Three historical axiom candidates failed current identifier resolution:
`AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1.Insts.CoreFmtDebug.fmt._native.decide.ax_7`,
`AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.Insts.CoreFmtDebug.fmt._native.decide.ax_1`, and
`AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.Insts.CoreFmtDebug.fmt._native.decide.ax_2`.
They are not silently counted as current declarations or accepted axioms.

## Validation, pins and handoff

All thirty attempts used the unchanged S2W host launchers in
`/home/dombarker/project-offloads/codex-cx-sound-int2-20261025`, with its pinned
object selection and caches. Each attempt had one scope, Lean `-j1 -M7000
-DElab.async=false`, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64.
All reservation checks admitted the scope on their first call. No concurrent
second scope was launched by this job. No Rust, Kani, extraction, SBF rebuild,
package build, manifest replay, timeout or memory-killed rerun occurred.

Exact per-target commands, source/dependency hashes, source revision, dirty
state, exit, wall time, peak RSS, swap, cgroup limits and full axiom output are
in `TAu_001`–`TAu_030` and `TAu_attempts.jsonl`. All query sources are preserved
byte-for-byte, including diagnostics; no new theorem was introduced.

Total compiler-command wall time: **110.71001157315914 seconds**; maximum RSS:
**5,440,596 KiB**; swap: **0**. Main endpoint query TAu_001: exit 0,
wall **4.845667042012792 seconds**, peak RSS **5,440,596 KiB**,
source revision `ac1f24d934` plus the exact dirty query snapshot/hash in its
receipt. TAu_002 (trust statements): exit 0, exact metrics in receipt.
A failed diagnostic scope is excluded from any “all green” claim; its successful
individual print messages are retained as observed diagnostics only.

No shipped source/harness changed, so the conditional three-ELF rebuild trigger
did not fire. Inherited artifact pins, **not newly reproduced by this audit**:

- default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`
- devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`
- Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`

No key, wallet, balance, account authority or refund was affected. No session A
worktree/candidate or other worker prefix was modified. Commits remain local;
no push or merge. Only TAu_ query/evidence files and this document changed.

**Next concrete deliverable:** resolve the stored-summary/provenance discrepancy
with L187's coherent selected-object replay; inspect the four missing circle
import headers; finish an exhaustive declaration/axiom census of that exact
environment, including external modules and failed/unavailable representatives;
then resolve or scope every nonstandard finding and W1 before closing L188.
An independent top-body axiom walk would also distinguish current kernel
contents from imported summary history, but no new introspection infrastructure
was built under this job. The budget is exhausted and no additional compiler
attempt is claimed. None of the parallel jobs is credited without an actual
merged theorem/association result.

Read-only receipt/recount verification passed with
`python3 evidence/trust-audit-20261026/TAu_validate.py`; results are recorded in
`TAu_validation.json`. `git diff --check` passed. Large temporary source maps
were retained by SHA256/size rather than committed; `TAu_seed.py` reconstructs
the checkout source input, and `TAu_inventory.py` records the scan recipe.
The exact executed query sources/receipts are authoritative, including spelling
repairs and excluded failures; regenerating a plan is not permission to repeat
an unchanged historical compiler invocation.
