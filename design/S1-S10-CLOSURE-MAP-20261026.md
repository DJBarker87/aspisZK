# S1–S10 closure map, 26 October 2026

**Full S1–S10 closure and deployed 100-bit soundness are not yet established.**
This is an audit of `AspisR1.Rc7_Top.deployed`, not a proof delivery. The source
baseline is `23069bb39431697e982852b34dc328b16b972e46`; audit receipts pin the
subsequent documentation-only revision and exact module/dependency hashes.
Concurrent results are not credited until integrated into this actual root.

## Definitions and counting boundary

The canonical numbering is the ten-row table in
[the cone audit](../docs/research/100bit-spend-path-20261013/design/CONE-AUDIT-20261021.md),
read with [C3-BIN](../docs/research/100bit-spend-path-20261013/design/C3-BIN-20261021.md),
[STATUS-CURRENT](../docs/research/100bit-spend-path-20261013/design/STATUS-CURRENT.md)
and [Session A handoff](../docs/research/100bit-spend-path-20261013/design/HANDOFF-SESSION-A-20261021.md).
These are provenance for names, not sufficient evidence of closure. In particular,
S6 is decoder/public/TX1/checkpoint (including forest/Claims consumers); S8 is
accumulator/residue/compact checking; S9 is factored Libra weights; S10 is
all sites/continuations including errors. Parser and multiproof are separate
cross-cone joins, not a canonical renaming of S8. General field primitives span
S3/S4/S5/S7/S9, not S9 alone. S10 artifact lowering is one sub-obligation.

The current [ledger](PREMISE-LEDGER-20261025.md#recount-on-rc7_topdeployed--2026-10-26)
and [expanded row inventory](../evidence/recount7-20261026/Rc7_premises.json)
control disposition. CLOSED means the listed independent implementation rows
are absent from the actual root, or a deployment row has the cited accepted
evidence retirement. It never means the retained trust items were proved.
OPEN means at least one relevant P row remains. TRUST labels only adopted T
rows, with the exact scope below. G is an experiment definition, not a proof
obligation or a trust discharge. Overlapping cone assignments are deliberate:
count row IDs once, not table mentions. `F3Y_G_Lnnn` is a **P** row despite its
historical name: its global world/submission/Evidence quantifiers differ from
native-local `Lnnn`. Each is independently required.

## Ten-cone matrix

All theorem names below are in namespace `AspisR1`. Audit numbers refer to
`evidence/s-map-20261026/SMap_NNN/{stdout.log,receipt.json}`; each named closure
support is checked by both `#check` and `#print axioms`. Historical retired
rows get zero new credit in this audit. Shared deployment rows are repeated
where they obstruct more than one cone.

| Cone and canonical obligation | Exact ledger families | Discharging theorem / evidence and remaining boundary | Status |
|---|---|---|---|
| **S1** preparation/transcript driver, Prepared/claim/scratch binding | Retired N001–N046 (immutable prepare owner), N108–N114 (queries/rho/canonical rho/alpha1), N115 (same saved Vec/model encoding); L122–L124/L126 (Prepared/alpha projections), L129–L132 (same input/query/read/decode), L139–L141 (claim/alpha), obsolete alias L168. | `SAP_PrepareOwner.installed`, `SAP_Binding.prepare`, `F3Y_InstalledLaws.prepare`, `SAP_SaveOnRun.saved`, `TxS_Encoding.model`; 002–005. Integrated claim/alpha projection uses `SAF_AcceptedValue.value` and root composition, 016/001/022. Authoritative retained evidence: `evidence/recount3-20261026/`, `evidence/recount4-20261026/`, `evidence/recount5-20261026/`, `evidence/recount7-20261026/`. This is closure of the installed accepted preparation row families, under D188/P6/library trust. S6 native public transport L176 and S2 runtime binding L159 remain separate shared deployment obligations. | **CLOSED** for these S1 row families; deployed claim remains gated by other cones. |
| **S2** dispatcher/adapter/header, same native caller and physical history | Retired L088–L093, L094–L098, L099, L155–L158, L160–L165, L180/L182–L184 and N117/N118; retained L159 (alias L185), L166, L181. T: L001–L082 and Rc5_T001. G: L083/L084, Rc5_G001–011. | `Rc7_Native.accepted`, `P2P_Release.remove`, `P2P_R6Result.strengthen`, `FGl_Join.accepted_raw_join_or_collision`, `FGl_Bound.bound`, `Rc7_Top.deployed`; 001/012/018–022. `CPH_Game.recordedInstance` / `CPH_Protection.derive`, 027–028, use the approved runtime game and persistence trust. Evidence: `evidence/recount7-20261026/`; retained CPH/P2P/FGl source chain. SCE_ covers L159/L185; BEf_ covers L166; L181 has no assigned covering job. | **OPEN**; named SDK/std/extraction/runtime/ROM portions **TRUST**, not caller closure. |
| **S3** row/group/Weights::pair | Retired N047–N074 (basis and E/K arithmetic), relevant N001–N046; L110–L128 primitive returns are outputs, L139–L141/L148 retired. Remaining L133–L138/L142/L144–L146 and corresponding F3Y_G_ rows. | `F3Y_InstalledLaws.primitives`, `Rc4_Assemble.deployed`, `Rc4_Cont.strengthen`, `Rc4_Literal.strengthen`, 006/009–010, remove query primitive hypotheses at the installed dictionary. `SAF_AcceptedValue.value` / `FGl_FinishProof.strengthen`, 016–017, remove canonicality requirement but **retain** round/pair/semantic meanings. Evidence: recount4/5/7. FIo_ is current owner dispatch for remaining finish families (ledger snapshot calls it FIn_). No theorem yet discharges these retained laws. | **OPEN** |
| **S4** four dots | Retired relevant basis/E/K/opening query primitive leaves N047–N088 and canonicality L148; remaining L143 and F3Y_G_L143; shared finish families L133–L138/L142 may consume its values. | Installed primitive/query composition 006/009–010; same root 001. These are not a proof of all22 `MatchingSupport.match0` equations. Evidence: recount4/7 and immutable source definitions. FIo_ must bind same source fold/openings to matching on both native-local and global domains. | **OPEN** |
| **S5** strict decode/tower/pairing/dot kernels | Retired N052–N069, N075–N079 and reached-return L110–L121/L125/L127/L128/L148. Remaining L133–L138/L142/L147 and corresponding F3Y_G_ rows. | 006–010 certify installed query arithmetic; 016–017 certify forward accepted finish transport without arbitrary reverse canonicality. Returned dot/quarter/eval values are existential outputs, not their mathematical meanings. Evidence: recount4/5/7. FIo_ must prove round boundary/quarter/eval, pair and dot at this installed FinishOps. | **OPEN** |
| **S6** decoder/public/TX1/checkpoint, including forest/Claims | Retired L091–L093/L099, L149/L150, L165, L171–L175/L177/L179 and N115; retained deployment L176. Relevant trust L078–L080/L191–L193 and Rc5_T001. | `NP6_ParsedPair.accepted_pair_unified`, `PFin_Packet.from_cut`, `P2P_R6Result.strengthen`, `SAP_SaveOnRun.saved`, `Rc7_Native.accepted`, 005/011–012/015/022. These connect the same accepted tuple and parsed Claims, with native unsafe helper certificates at the selected NP6 dictionary; they do not prove L176's native decoded/public ownership/error/cleanup/adoption. Evidence: `evidence/native-p6-20261026/` source packet as pinned by `evidence/recount7-20261026/Rc7_inherited_evidence.json`, recount6/7; the source pins are independently rechecked in `SMap_artifact_audit.json`. L176 is **UNCOVERED**. | **OPEN** |
| **S7** query values/geometry/inverses/batched accumulation and matching | Retired N047–N107; L149/L150, L169/L170; remaining L143/F3Y_G_L143, shared L159/L166/L181. | `F3Y_InstalledLaws.primitives/canonical/domain/multiply/one/inverse`, `Rc4_Assemble.deployed`, `Rc4_Cont.strengthen`, `Rc4_Literal.strengthen`, 006–010; installed ten/twelve accumulation composition is checked through 001/022. Evidence: recount4/7. FIo_ covers matching; SCE_ runtime carrier, BEf_ batch; oracle prefix row remains uncovered. Reference-query totality alone cannot retire those rows. | **OPEN** |
| **S8** accumulator/residue/compact finish; parser/multiproof joins shared with S2 | Retired L100–L109/L149/L150/L170/L173, L195–L199; remaining L147/F3Y_G_L147 plus L166/L181 and L159 for whole experiment. | `P6C_Extension.boundary`, `P6C_Extension.source_preserved`, `P6C_FullBoundary.same_cuts`, 013–014; parser/Claims joins 011–012/015; `SAF_AcceptedValue.value`, 016, still assumes dot meaning. Evidence: recount6/7 and inherited P6 certificates. FIo_ covers actual dot semantics, BEf_ full batch Result/effects, SCE_ runtime carrier; L181 uncovered. Mathematical P6 callback closure is not full rejected native-prefix closure. | **OPEN** |
| **S9** factored Libra weights | Retired N070–N074 and preparation/canonicality subrows; remaining L142/L144–L146, corresponding F3Y_G_ rows, with round laws L133–L138 shared. | Installed arithmetic support 006/009–010 and accepted finish transport 016–017 are compiled; `FGl_PreparedAt.Owners` still requires exact dual-fold pair and semantic initial/chain/terminal equations. Evidence: recount5/7 and `lean/FGl_FinishLeaves.lean`. Generic semiring identities do not instantiate these source laws. FIo_ covers them. | **OPEN** |
| **S10** all source sites and continuations, including errors; artifact correspondence | L186 retired; L166/L176/L181 remain semantic coverage rows; L187/L188 are separate release gates. T: L189/L190 plus extraction L078–L080. | L186 **CLOSED by accepted evidence**, with no applicable Lean compiler-correctness theorem to #check: `evidence/lowering2-20261026/Low2_source_to_elf_manifest.json` and `Low2_final_receipt.json`, three rebuilt pins and140 ordering facts under retained P7. Concrete source/dictionary joins are checked by 001/013–015/021–022/029. No theorem proves compiler correctness, and no declaration turns unresolved error/ownership/oracle continuation rows into inventory coverage. BEf_ covers L166; L176/L181 uncovered. | **OPEN** overall; lowering subrow **CLOSED**, P7/P6 **TRUST**. |

The retired S1 claims are for the actual source-selected sampler/context,
not an unconditional theorem for arbitrary independent q/tr/data/rho values.
The Rc3 recount explicitly distinguishes its source specialization from that
stronger universal continuation. Likewise L155's retirement repaired a false
logical-public interface, and frozen2 L157 was false for deployed physical
public hashing: neither is a proved old statement. The owner-approved frozen3
replacement and charged-collision alternative are the current domain and
conclusion. `Rc7_Reverse.same_witnesses` supplies only the checked clean-world
reverse transport, not unconditional implication to the old exact-log headline.

## Exact open rows and covering work

This table exhausts all32 retained P audit rows (31 independent after alias
L185). FIo_ is the finish job named in this dispatch; the pinned Rc7 ledger
uses FIn_. This name update is a coverage assignment, not evidence that either
job has landed. RPz_ is assigned the coherent replay in this dispatch; the
pinned ledger still says UNCOVERED. No concurrent worktree was accessed.

| Row IDs | Exact remaining law | Cones / covering job |
|---|---|---|
| L133, F3Y_G_L133 | round0.boundary | S3/S5/S9; FIo_ |
| L134, F3Y_G_L134 | round0.quarter | S3/S5/S9; FIo_ |
| L135, F3Y_G_L135 | round0.eval | S3/S5/S9; FIo_ |
| L136, F3Y_G_L136 | round1.boundary | S3/S5/S9; FIo_ |
| L137, F3Y_G_L137 | round1.quarter | S3/S5/S9; FIo_ |
| L138, F3Y_G_L138 | round1.eval | S3/S5/S9; FIo_ |
| L142, F3Y_G_L142 | exact pair / dual-fold dot | S3/S5/S9; FIo_ |
| L143, F3Y_G_L143 | all22 MatchingSupport.match0 equations | S4/S7; FIo_ |
| L144, F3Y_G_L144 | semantic EquationEndpoint.initial | S3/S9; FIo_ |
| L145, F3Y_G_L145 | semantic EquationEndpoint.chain | S3/S9; FIo_ |
| L146, F3Y_G_L146 | semantic EquationEndpoint.terminal | S3/S9; FIo_ |
| L147, F3Y_G_L147 | exact source dot on final64 values and actual weights | S5/S8; FIo_ |
| L154 | hqueries: prover log length bounded by Q0+Q1 for every H | External adversary-budget interface; **UNCOVERED** concrete deployment association; not a cryptographic assumption |
| L159 | frozen3 StoredCarrierBinding for this source/prover/runtime | S2, shared whole experiment; SCE_ |
| L166 | complete source batch Result/effects/carrier/rejected-prefix | S2/S7, multiproof join/S10; BEf_ |
| L176 | S6 native decoded/public transport, ownership/error/cleanup/adoption | S6/S10; **UNCOVERED** |
| L181 | full oracle order/duplicate/early exit/rejected-prefix runtime experiment transport | S2/S10, all oracle-using joins; **UNCOVERED** |
| L185 | deployed stored experiment | Alias of L159; SCE_, **zero extra independent credit** |
| L187 | coherent frozen dependency replay | Separate release gate; RPz_ dispatch, no completion credited |
| L188 | release-wide axioms/trust/adoption audit | Separate release gate; lead, **UNCOVERED** |

For each of these P families the answer to “which theorem discharges it?” is
**none at Rc7**. Checked conditional consumer theorems are not discharges.
In particular, `FGl_PreparedAt.Owners` expands to twelve globally quantified
families; packing them into one binder cannot remove24 native+global rows.

## Accepted trust boundary (89 independent T rows)

The [binding contract](../docs/research/100bit-spend-path-20261013/design/SECURITY-CONTRACT-20261021.md)
retains the fixed security game and cryptographic model; its **Owner-approved
amendment, 2026-10-26**, explicitly adopts frozen3, the two-transaction game
(a)–(d), and RuntimePersistence. Existing tool/library/runtime trust is
separately affirmed in C3-BIN's **2026-10-26 closure instructions**, item4;
its **2026-10-25 13:35** ruling specifies P7 lowering; its **2026-10-23 01:20**
route-B addendum specifies SdkBorrow. The contract is not blanket approval to
trust a missing implementation refinement.

| Exact rows | TRUST item and citation / scope |
|---|---|
| L001–L034 | S2TrustedSdkBorrow, fifteen documented fields expanded into34 atomic reply/state/identity laws; C3-BIN route B, 2026-10-23 01:20. No caller output/log/success conclusion is trusted. |
| L035 | TrustedStd.slice_copy_from_slice; C3-BIN route-B addendum cites D133/D145, and closure instructions item4 retain TrustedStd. |
| L036–L056, L057–L077 | RuntimeEntrypointAdmission for the two entries: valid typed heap, guard/account relation, fresh guards and related runtime state; C3-BIN closure instructions item4, retained runtime boundary. |
| L078–L080 | D188 AeneasExtraction stage1/stage2/digestSource association at the exact installed dictionary; C3-BIN afternoon25October ruling and 26October Vec/Box ruling. Unsafe uninit/raw writes require P6 certificates, not this safe-library interpretation. |
| L081 | P1 ideal-oracle realization; fixed security contract, cryptographic model. No deterministic SHA256 random-function theorem is asserted. |
| L082 | RuntimeSyscall hashv/flattened-byte SHA256 law; retained runtime trust, C3-BIN closure instructions item4. |
| Rc5_T001 | RuntimePersistence = CPR_DataPersistence.TwoTransactionLaw; Security Contract owner amendment item3; `design/RUNTIME-PERSISTENCE-ITEM-20261026.md`. Ordinary-account data bytes only, final parent success/rollback and zero-lamport absence; no owner/balance/privilege/SDK theorem. |
| L189 | P7 rustc/LLVM/SBF toolchain, exact pinned versions/flags; C3-BIN 25October13:35. L186 retirement under this trust does not prove compiler correctness. |
| L190 | P6/Kani source-step association, retained scope; C3-BIN closure instructions item4 and native Vec/Box ruling. Mathematical callback theorems do not prove the verification tool. |
| L191 | Runtime allocator, entrypoint, syscall, abort/rollback/private allocator separation; C3-BIN closure instructions item4. |
| L192, L193 | TrustedStd.option_ok_or / result_unwrap32, full Result/failure semantics; same adopted TrustedStd boundary. |
| L194 | Fixed cryptographic security contract / ideal-oracle assumptions and collision accounting; binding SECURITY-CONTRACT. |

Counts:83 actual T +6 deployment T =89. None was added, removed or widened by
this audit. Standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`)
are a separate kernel-foundation audit, not these runtime/tool assumptions.

## Release gates independent of cone labels

| Gate | Evidence needed before final claim | Current state |
|---|---|---|
| L187 coherent replay | Exact final dependency/source closure after remaining jobs integrate; exit, wall, aggregate RSS, swap, revision and axioms with frozen object provenance | **OPEN**. Focused cache checks here are not a replay. RPz_ completion must be reviewed on the final root. |
| L188 final audit | Release-wide accepted axioms, every explicit trust item and its concrete instance, all source/model/adoption and artifact pins | **OPEN**. Fresh standard-only checks of selected theorem names do not settle the complete boundary. |
| Joint fixture / JFw_ | One common installed dictionary and physical two-transaction execution satisfying all retained release premises simultaneously, including game and native acceptances | **OPEN**. Not an extra P deduction; an independent non-vacuity gate. |

Class G is exactly L083/L084 and Rc5_G001–Rc5_G011: accepted1/accepted2,
consecutive entries, entry identities, checkpoint bank/public keys, no intervening
transaction, successful parent, and recorded copy/actions/writer/reader traces.
They state the approved game; no logical hypothesis vanished when these13 rows
were reclassified. JFw_ must inhabit them together with the other premises.

## Before/after, recount and non-vacuity

**Before and after this audit are identical:**
`AspisR1.Rc7_Top.deployed`, with the same quantifiers, native entries, installed
dictionary, submitted bytes, physical public carrier, failure event, trust
items and constants. [SMap_BEFORE.lean.txt](../evidence/s-map-20261026/SMap_BEFORE.lean.txt)
and [SMap_AFTER.lean.txt](../evidence/s-map-20261026/SMap_AFTER.lean.txt) are
byte-identical retained complete Rc7 statement transcripts, checked against
the fresh root inventory001. The transcript is reused, not falsely presented
as a fresh full-print run. No new theorem or premise removal is claimed.

In compact form, both statements take SDK/std/entry/extraction/hash/runtime
laws, two accepted native wrappers, the approved game and RuntimePersistence,
query bound, global finish owners and frozen3 StoredCarrierBinding; their
output is the one native witness tuple and source/caller/physical facts,
collision-aware log/result transport and the frozen3 failure bound. Conditional
native-local arithmetic remains inside the exported continuation. FGl and
P2Prime share the same recorded Q+2965 collision event; no extra account event
or account/source equality premise is introduced. At zero prover queries the
conditional whole-experiment bound is strictly below2^-100, with the proved
positive margin; repeated attempts keep the explicit Q dependence. This is
not an unconditional security statement about the deployed verifier.

Ledger method: expand law-bearing structures/conditional continuations;
retain guards and quantifier domains; count distinct atomic families once;
separate antecedent/deployment/alias, T/P/G and owner; never count conclusions
as premises. Historical Rc6→Rc7 (same G classification) was actual
83T/19P/13G→83T/26P/13G, net+7P (five removed, twelve global families added);
deduplicated89T/27P/13G→89T/31P/13G, net+4P after three deployment retirements.
The raw L182 alias receives no extra credit. **This audit's delta is0T/0P/0G/0C.**
Before=after: actual83T/26P/13G; deployment6T/5P; one deployment P alias;
all retained89T/32P/13G; deduplicated89T/31P/13G. No security-percentage claim
follows from these counts.

Fresh non-vacuity checks024–026/023 validate
`Rc7_Nonvacuity.composed`, `Rc7_Clean.exists_world`,
`Rc7_AcceptedInput.accepted_input`, and `Rc7_Reverse.same_witnesses` with their
actual hypotheses. `composed` uses a constant byte prover and constructed
fixture runtime whose binding is proved, but still assumes accepted native
wrappers, finishOwners and same-cut snapshot identities. `exists_world` rules
out a universal collision alternative; `accepted_input` rules out an
always-rejecting driver conditional on the native acceptance premise.
These do **not** prove joint inhabitation of all release premises. That is
why JFw_ remains required. Source review of `lean/FGl_PreparedAt.lean` and
`lean/FGl_FinishLeaves.lean` confirms the12 global laws are still premises,
including the semantic terminal equation; nothing was silently trusted.

## Validation and provenance

Used the full audit budget: **30/30 Lean invocations,40 theorem checks,0/0
Kani**. All30 exit0. Total Lean wall91.544851s, maximum per-process
RSS5,469,128KiB, swap0; all printed theorem dependencies are subsets
of `[propext, Classical.choice, Quot.sound]`. There are no new theorems.
Each invocation contains only imports, `#check`, and `#print axioms`.
No full replay or Rust/SBF compilation was run. The budget is exhausted;
no additional Lean invocation is authorized by this audit allocation.

Each attempt's exact command/target, source revision and SHA256, selected
object/sidecar/dependency fingerprint, exit, wall, RSS, swap, cgroup limits
and complete axioms lines are in
[evidence/s-map-20261026/](../evidence/s-map-20261026/), indexed by
[SMap_ATTEMPTS.jsonl](../evidence/s-map-20261026/SMap_ATTEMPTS.jsonl) and
[SMap_plan.json](../evidence/s-map-20261026/SMap_plan.json).
The coherent host workspace is the one pinned by
`evidence/sound-int2-20261025/HANDOFF.md`; unchanged selected objects and
package/core caches were reused. No missing dependency build was needed.
Each job used one existing-launcher scope at a time:
MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64,
`lake env lean -j1 -M7000 -DElab.async=false`. Admission logs were redirected
on the host before transfer; no barrier refusal/retry, cap increase, timeout,
memory kill or unchanged repeated compilation occurred. Each new module has
a distinct audit subject. This is focused cached validation, not L187.

[SMap_rows.json](../evidence/s-map-20261026/SMap_rows.json) exhaustively maps
all134 retained audit rows to cone/shared boundary and coverage, with the
original ledger hash and counts. [SMap_validation.json](../evidence/s-map-20261026/SMap_validation.json)
records the30-run summary. [SMap_artifact_audit.json](../evidence/s-map-20261026/SMap_artifact_audit.json)
records an independent read-only source/receipt comparison:1,243 compiler
input files,18 NP6 theorem sources, pinned packet source snapshots and
retained three-build artifacts/140 ordering observations. It does not claim
new build or order-collector execution. The old NP6 checker ledger-hash
mismatch is preserved and disclosed; foreign manifests/receipts were never
rewritten to make a checker pass. A dedicated read-only comparison avoids
running the Low2 checker that writes into another worker's evidence directory.

L186's reused artifact pins are:

- default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`
- devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`
- Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`

Only SMap audit modules/receipts and this map changed. No shipped or cfg(kani)
file changed, so no ELF rebuild trigger arose. No session A live worktree,
candidate, wallet/key/account or other worker's files were changed. Source
inspection and fresh checks establish this map; handoff prose alone is not
closure evidence. Stage commits are local, with no push.

Once every open S-cone row above lands in the actual top theorem, the retained
query-budget and runtime experiment interfaces are concretely associated,
and L187/L188 plus the joint fixture pass, “S1–S10 closed” would mean a
source-connected, artifact-pinned classical soundness argument for the
owner-approved frozen3 two-transaction spend game, under the explicit trust
boundary: whole-experiment zero-query error at most2^-100 and the explicit
repeated/adaptive-attempt Q-dependent bound without grinding credit. It would
still not establish privacy, knowledge/custody/availability properties outside
that contract, or Stream B. Those remain separate programmes; no collection
of closed soundness rows silently establishes them.

## Rc8 installed-top status update — 2026-10-26

This appended section supersedes the status column above for the integrated
root `AspisR1.Rc8_Top.deployed`; earlier sections are preserved verbatim.
**Full deployed 100-bit soundness remains not established.** Concurrent
SCH_/FIp_/BEf_/JFt_/RPz2_ results receive no completion credit here.

The root now uses `FIo_Install.configuration` throughout: complete native Pair,
FIn constructor/arithmetic/dot, and the SAME native inputs, saved checkpoint,
selected physical events, source/prover/runtime and Q+2965 charged event.
`Rc8_Install.native_headline/arithmetic/complete_pair` check compatibility;
`Rc8_Transport.baseline_conclusion` returns the full prior conclusion on this
installation, and `Rc8_Reverse.same_witnesses` retains clean-event reverse
transport on its actual existential tuple. No old frozen2 exact-log statement
is silently restored.

| Cone | Status at Rc8 | Recount basis / checked closure support |
|---|---|---|
| S1 | **CLOSED for the previously listed accepted preparation families** | No new S1 credit. `SAP_PrepareOwner.installed`, `SAP_Binding.prepare`, `F3Y_InstalledLaws.prepare`, `SAP_SaveOnRun.saved`, `TxS_Encoding.model`, `SAF_AcceptedValue.value`; fresh `#check` and axioms in Rc8_ClosureChecks. Remaining whole-experiment rows stay separate. |
| S2 | **OPEN; adopted library/runtime portions TRUST** | L159/L185/L181 SCH_, L166 BEf_; same RuntimePersistence and game. The root composes six distinct global finish discharges, but runtime association and rejected-prefix transport remain. |
| S3 | **OPEN** | Native-local L133–L138/L142/L144–L146 remain; global F3Y_G_L142/L144–L146 remain. Four global boundary/eval families, the shared global quarter law and global dot are now absent. |
| S4 | **OPEN** | L143 and F3Y_G_L143 remain: all22 SAME-view matching equations, assigned FIp_. |
| S5 | **OPEN** | Native rounds, Pair and dot remain. Global rounds/dot are discharged by `FGm_Aligned.values` → `FGm_Join.accepted_raw_join_or_collision` → actual Rc8 top, checked in Rc8_ClosureChecks. This is not native-local closure. |
| S6 | **CLOSED for the listed decoder/public/TX1/checkpoint row families, under retained trust** | L176 is retired by the accepted S6N native packet and `S6N_Installation.facts/accepted`; complete decoder and getters checked as `S6N_Decoder.complete`, `S6N_Getters.complete`. The certificate is a conclusion of the actual top at the same installed dictionary. D188/P6/runtime/tool/source pins remain trust boundaries. |
| S7 | **OPEN** | L143/F3Y_G_L143, L159/L166/L181 remain; installed primitive and geometry closures are unchanged. |
| S8 | **OPEN** | Native-local L147 plus L159/L166/L181 remain. F3Y_G_L147 is absent; no native-local dot removal is claimed. |
| S9 | **OPEN** | L142/L144–L146 and global counterparts remain; native round families remain. Complete Pair installation alone is not FunctionalWeights/dual-fold value identity. |
| S10 | **OPEN** | L166/L181 and release gates L187/L188 remain. S6 deployment L176 retired. Historical lowering receipts/pins are reused; no new compiler-correctness theorem or artifact rebuild is claimed. |

Every CLOSED theorem claim in this appended table has a fresh `#check` and
`#print axioms` in `evidence/recount8-20261026/Rc8_055/stdout.log`.
The concrete native source/tool evidence for L176 is reused from
`evidence/s6-native-20261026/`, not replaced by these mathematical checks.

Fresh recount: raw actual **83T/19P/13G**, deployment **6T/4P**, one
L185 deployment alias. Excluding L185 gives **89T/23P/13G**; additionally
identifying the two identical native quarter predicates L134/L137 gives
**89T/22P/13G**. On that same independent-family basis Rc7 was
**89T/29P/13G**, so delta **−7P**, no T/G/C change. Counts by owner and all
row IDs are in `Rc8_premises.json`; `Rc8_LEDGER.md` tags every remaining P
with a covering job or UNCOVERED. Native-local and global domains are never
merged merely because they share an L-number suffix.

JFt_ joint fixture remains OPEN, separate from the row totals. Checked
`Rc8_Nonvacuity.composed` uses this actual root with SAME accepted native
cuts/snapshots and supplies accepted source/runtime executions and positive
zero-query margin, conditional on the five retained global families and
other existing premises. `Rc8_Clean.exists_world` rules out an always-bad
collision event. Neither proves joint release inhabitation. L187 RPz2_
and L188 UNCOVERED remain release gates; SCH_/FIp_/BEf_ remain assignments.
