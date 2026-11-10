# NPO_ handoff: the host re-instantiated at the deployed program ids

This is Stream A job NPO_, dated 2026-11-10. It ran in worktree cx-integrate (branch
codex/cx-integrate-20261107) after `git merge --no-edit research`, which fast-forwarded to 2afa7a98bf3.
The host workspace was /home/dombarker/project-offloads/codex-cx-hostids-20261110. Its LEAN_PATH was
the workspace's own out/, then the L187 replayed objs/ and base_ref/, by reference; nothing was copied
from the closure. No merged module was edited. Target not yet established.

## 0. Summary

FINDING F1 of NPN_ is resolved at the model level. The run-7 top theorems now exist, kernel-checked,
at a host built from the 10 November 2026 devnet ids. A second instance uses the 29 October ids.

The procedure had three steps. First, a native walker found every constant in the cone of the run-7
roots that depends on the id constants: 718 of 146,554 reachable constants. Second, each of those 718
was copied with the three id constants replaced and every reference renamed. Third, every copy was
sent to the kernel (`Kernel.Environment.addDeclCore`, full checking).

- 717 copies re-checked with their original proof term unchanged. These are the parametric ones: the
  id is only passed through.
- One theorem is literal: `AspisR1.CPH_Program.not_system`. Its proof compares the head byte 95 of
  7Q2nGsPg with 0. It is restated with the new head byte as `NPO_DeployedIds.not_systemNov` (235)
  and `not_systemOct` (170).
- The ledger rows that compare ids were proved parametrically. These are TX2:234 (pool, registry and
  entry) and TX1:345 (checkpoint owner). Neither depends on the literal ids.

The kernel statements of the re-instantiated `deployed_splitB`, `deployed_charge`, `fail_sub_rec` and
`NNH8_DeployedOuter` equal TAS_FinalB's verbatim kernel statements once the re-instantiated host
constants are renamed back (Expr equality, 8/8). The pinned walker's axiom walk of all eight is
standard.

Continuation (section 8, after the lead merged the first round):

- `leanchecker` replays NPO_CloneNov and NPO_CloneOct with exit 0. A negative control with one
  unchecked, ill-typed theorem is rejected, so the replay has teeth.
- The corrected restatement module NPO_FinalB.lean (v2, with the short alias names) compiled with exit
  0 in the second authorised 16 GiB scope. Every alias has standard axioms.
- The executable check (task step 4) is still not run. NPO_COMPUTABLE_SCOPING.md scopes the computable
  host instance it needs.

## 1. Id map

The ids were decoded by NPO_base58.py, using the standard alphabet with a round-trip check. The decoder
was validated against three pinned values:

- `CPH_Program.verifier` decodes to 7Q2nGsPg…;
- `NHJ_IdPacket.poolDevnet` decodes to BmsNikL9…;
- `NHJ_IdPacket.registryDevnet` decodes to 9pWwAcBg….

It also re-derives the placeholders 0x41^32 = 5PjDJaGf… and 0x44^32 = 5bV6jUfh….

| Model constant | Old value | 10 November (`…Nov`) | 29 October (`…Oct`) |
|---|---|---|---|
| `CPH_Program.verifier` (program arg, data.program) | 7Q2nGsPg… (July V7) | GqZzWuGTojfsxYnDzmyWKhdPGkce19xN1Txu9Vgnr5hy | CSnhzGdHQuzMW512CSunJzHrutcmh8ZAFzqx2z1zKorQ |
| `NHJ_IdPacket.poolDefault`, i.e. `D.pool` | 0x41^32 | 37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt | BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs (= `poolDevnet`, rfl) |
| `NHJ_IdPacket.registryDefault`, i.e. `D.registry` | 0x44^32 | 9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q | 9pWwAcBg… (= `registryDevnet`, rfl) |

**Correction to the brief.** The brief gave the 10 November registry as Hnn3D6DS…, but `D.registry` is
the registry **program** id. Hnn3D6DS… is the registry **account** under program 9pWwAcBg…. The
evidence:

- `D` = `LIB_Deployed.ids false` carries the verifier's `AUDIT_POOL_PROGRAM` / `AUDIT_REGISTRY_PROGRAM`
  .rodata slots (r1_pool_adapter.rs, ASPIS_R1_POOL_PROGRAM_ID / ASPIS_R1_REGISTRY_PROGRAM_ID).
- RSL TX2_234 compares `p.registry_program` and `r.registry_program` with `D.registry`.
- NPC_DEVNET_RESULT states that 2331ad8a differs from 63ad3e9c only in the Pool-id slot, so its
  registry-id slot is still 9pWwAcBg….
- The 10 November recording names its programs {verifier GqZz…, pool 37hd…, registry 9pWw…}.

NPO_id_check.py writes NPO_ID_RECORDING_CHECK.json from the 10 November transfer pair. It finds:

- the TX1 checkpoint GW4wYgac is owned by GqZz…;
- master D7akkxLF holds the registry program at offset 216;
- registry account Hnn3D6DS holds 9pWw… at offset 120;
- entry 2DrbrBFV holds the verifier GqZz… at offset 40.

These are the positions NPN F1 listed.

## 2. Dependency map (NPO_ID_DEPENDENTS.json)

The walk is NPO_L005, re-done with projections in NPO_L015. It covers the replayed L187 objects from
the roots `TAS_FinalB.deployed_splitB`, `deployed_charge`, `fail_sub_rec` and `NNH8_DeployedOuter`.

- **Counts.** 146,554 reachable constants; 718 dependents: 468 theorems, 225 definitions, 12 inductives
  with 12 constructors, and `not_system`.
- **Classification.** It is decided by the kernel re-check, not by inspection. A dependent is parametric
  if its unchanged proof term checks at the new ids, and literal if the kernel rejects it.
- **Result.** 717 are parametric and 1 is literal (`CPH_Program.not_system`; the kernel error is
  recorded in the JSON).

**How the ids enter.** Only through the host instantiation:

- `CPH_Program.verifier` enters through NOC_Run5bHost: args1/args2 program, `data.program`, Queries,
  event, Concl and select. It also enters the NNH8_/ARX_/FJp_/RPx_ host chains.
- `D` enters by two paths:
  - through `LIB_Deployed.deployed` into `LIBB_PoolLib.deployed` and `LIB_Instances.D`, and from there
    into `NNH_Run6Installed.implementation` and `NNH_Libraries.D`;
  - through `NHJ_IdPacket.pool/registry false` into `NNH_Tx2Configuration.select` and
    `NNH_Tx2ModelSlots.install`, which set op45/op46 of the host sdk. TX1 objects that range over the
    host configuration (NOC_Stage1Inv and others) therefore mention `D` too, without comparing it.
- The extracted `NHJ_IdReference.ids_ref` is not in the cone.

**Ledger rows.**

- TX2:234 (RSL `policyBad`, `registryV2Bad`, `Ref`, `RowSpec_234`) takes `D : DeployedIds` as an
  argument. The entry check compares `e.verifier_program` with the argument `a.verifier_program`.
- TX1:345 checks `verifierCheckpoint ck a.program_id`, where `a.program_id` is the argument.
- No TX2_234 or TX1_345 constant depends on the ids.
- No ledger30 NNN_* source mentions them (grep).

## 3. Delivered constants

| Artifact | sha256 | Contents |
|---|---|---|
| out/NPO_DeployedIds.olean (src NPO_DeployedIds.lean 2d484d91…) | 8344da74… | `verifierNov/Oct`, `poolNov/Oct`, `registryNov/Oct`, `DNov`, `DOct`; rfl: `poolOct_devnet`, `registryOct_devnet`, `registry_same`, `DOct_devnet` (= `LIB_Deployed.devnet`); `not_systemNov/Oct` |
| out/NPO_CloneNov.olean (NPO_L015) | ccdf4987… | 705 kernel-checked declarations under prefix `NPO_Nov.` |
| out/NPO_CloneOct.olean (NPO_L016) | 40112a70… | the same under `NPO_Oct.` |

The table below gives, for each name the brief asked for, the 10 November constant that is delivered.
The 29 October constants are the same with prefix `NPO_Oct.`.

| Requested name | Delivered constant |
|---|---|
| NPO_Program.verifier | `NPO_DeployedIds.verifierNov` |
| NPO_Instances.D | `NPO_Nov.LIB_Instances.D` (= `NPO_Nov.LIB_Deployed.deployed`; elaborated rfl `= NPO_DeployedIds.DNov` in L018) |
| NPO_Run5bHost.S_host | `NPO_Nov.AspisR1.NOC_Run5bHost.S_host` |
| implementation | `NPO_Nov.AspisR1.NNH_Run6Installed.implementation` |
| A1 field | `NPO_Nov.AspisR1.NOQ_FinalCombined.field` |
| A2 field | `NPO_Nov.AspisR1.NOF_A2FieldCorrected.field` |
| rest | `NPO_Nov.AspisR1.NNH8_Rest.assemble` |
| NPO_FinalB.deployed_splitB | `NPO_Nov.AspisR1.TAS_FinalB.deployed_splitB` |
| NPO_FinalB.deployed_charge | `NPO_Nov.AspisR1.TAS_FinalB.deployed_charge` |
| fail_sub_rec | `NPO_Nov.AspisR1.TAS_FinalB.fail_sub_rec` |
| NNH8_DeployedOuter | `NPO_Nov.AspisR1.NNH8_DeployedOuter` |

Each copy is the original declaration with the three id constants replaced and the dependents
renamed. The theorems are therefore "assembled as TAS_FinalB did": the same `NNH8_Top.deployed_splitB_of`
application, the same field terms, and the same 700-odd sub-proofs, re-checked by the kernel at the new
ids. The short names in the left column now exist as aliases in out/NPO_FinalB.olean (v2, NPO_L031;
section 8).

**Kernel statements.** These are in NPO_L020/NPO_STMT_<Inst>_<root>.{orig,clone}.txt, printed with
`pp.all` and `pp.proofs false`. The NPO_L020 reader found three things.

1. For all 8 roots, renaming `NPO_<Inst>.X` to X and the three new ids to the old ones turns the copy's
   kernel type into the original's exactly (`Expr` equality).
2. The constants that differ in the statements are the host constants `NOC_Run5bHost.S_host`,
   `NNH8_Exec.exec`, `NNH8_Exec.recSig`, `NNH_Run6Installed.implementation` and
   `NNH8_HeadlineB.headlineB`. `deployed_splitB` also has `NNH8_Split.rest`; `deployed_charge` also has
   `NNH8_RecorderFixed.fixedProgram` and `NOC_Run5bHost.runtime`. Nothing else differs. All binders
   (L0, borrow, copy, std, allocation217/234, ch, alloc2, fx, w/wOf, H, anchor, queries, run/fail)
   keep their types and universal status.
3. Each `.orig.txt` equals TAS_G0_AUDIT.json `kernel_statements_verbatim` up to whitespace, and each
   `.clone.txt` equals its `.orig.txt` with the prefix removed (NPO_STATEMENT_TEXT_DIFF.json).

The statements name no id directly. The ids sit inside the definitions of those host constants, so the
statement differs from TAS_FinalB only through the id constants.

**Axioms.**

| Check | Result |
|---|---|
| `collectAxioms` (L020) and the pinned walker NNM_ProofDriver 46ee271b…, raw ax2 (Nov L021, Oct L025) | [propext, Classical.choice, Quot.sound] for all 8 roots |
| Walker `equal` | true for all 8 |
| Reachable constants, Nov | 146,418 / 146,599 / 146,419 / 146,425, against 146,370 / 146,551 / 146,371 / 146,377 for TAS_FinalB |
| Reachable constants, Oct | 146,423 / 146,604 / 146,424 / 146,430 |
| sorry | none |

The reachable lists are retained as .xz files with the sha256 of each uncompressed list.

**Before and after.** Old: `deployed_splitB … (run : Runs (NOC_Run5bHost.S_host L0 copy std)
(implementation …) (ctxB (NNH8_Exec.exec L0 copy std) fx w H)) : …`. New: the identical text with
those host constants replaced by their `NPO_Nov.` copies. The quantifiers, carriers, failure event
and conclusion are unchanged. No hypothesis was added or removed.

This is a model-fidelity correction (AGENTS section 4): the host now names the deployed image. It is
not a premise discharge, and it is a statement change.

**What the 10 November instance represents.** The model has no separate verifier-ELF constant for the
Pool id; it carries that id as `D.pool` (op45). 2331ad8a differs from the pinned 63ad3e9c only in that
slot. The Nov instance is therefore the model's representation of the 2331ad8a image at GqZz…. Whether
the contract treats 2331ad8a as the frozen verifier is still the open lead/owner question from
NPC_DEVNET_RESULT. The Oct instance is the pinned 63ad3e9c image at CSnhz…, where `D` = `LIB_Deployed.devnet` by rfl.

## 4. The textual restatement that failed (NPO_L017, NPO_L018)

NPO_FinalB.lean (generated by NPO_gen_final.py) restates TAS_FinalB's run-7 text with the host replaced
and proves each statement by the copy. It also adds the named aliases and some rfl checks.

**The 8G attempt.** NPO_L017, the Nov half alone in the 8G scope, was killed by `-M7000` during the
import. This is F5: TAS_FinalB plus the copy sits at 7.35 GB.

**The 16 GiB attempt.** NPO_L018 was the one authorised 16 GiB scope (MemoryHigh 14G, MemoryMax 16G,
`-M15000`). It peaked at 7,371,868 KiB and exited 1.

| Outcome | Declarations |
|---|---|
| Elaborated and kernel-checked, standard axioms | `not_systemNov/Oct`; `D_eq` (both); `D_devnet` (Oct = `LIB_Deployed.devnet`); `type_same` (S_host has the original's type); `args1_at` / `args2_at` (args1 c = `NNE_EntryArgs.args c.i.entry 3 verifierNov c.i.data`, likewise args2 with 7; the restated literal field); `fail_sub_rec` restated textually and proved by the copy (both instances) |
| `ctx_same` | whnf heartbeat timeout. Not needed. |
| `deployed_splitB` | "Ambiguous term". The generator added `open FS FS2 …` before it; TAS_FinalB adds those only before `deployed_charge`. The theorem was then accepted with sorryAx and the module failed. |
| `deployed_charge` | defeq timeout. The generator mapped `NNH8_RecorderFixed.fixedProgram` to the original, but it is a copy, so the textual statement differed from the copy's. NPO_L020 confirms the copy's statement is right. |

The compiler PANIC lines in the log come from compiling `abbrev`s over the copies. The copies carry no
IR and no noncomputable tag. These are not errors.

No further 16 GiB scope was used. The delivered theorems are the kernel-checked copies listed in
section 3. Two generator fixes and one deletion would make a textual module elaborate:

1. rename `fixedProgram`;
2. keep TAS_FinalB's open order;
3. drop `ctx_same`.

That module would still need a 16 GiB scope, which is the lead's decision.

## 5. Executable check (task step 4): not run

NPO_L022 is a computability triage, labelled as such and not as a proof. The extracted
`AdapterRw.r1_pool_adapter.owned.stage1_owned` compiles, but the following are marked noncomputable:

- `NOC_Run5bCtx.sdk` (the host dictionary);
- `NNH_ReturnsBundle.tx1Value` and `tx2Value`;
- `NNG_TotalProducer345.producer`;
- `NNH_Run6Installed.implementation`.

The copies have no code at all.

A compiled run of the Lean model on the recorded bytes therefore needs a computable host instance
first: a computable sdk with H taken as a table, pda and clock as tables, and the allocation streams.
Its agreement with `NOC_Run5bCtx.sdk` on the reached slots would have to be proved or checked. That
cannot be done in 2 to 4 scopes.

NPO_L024 listed the noncomputable leaves under these roots. That list included `List.flatten`, and I
called it unreliable. That was wrong: `List.flatten` is declared `noncomputable` in Init/Prelude.lean
and runs through a `@[csimp]` replacement. The full classification is NPO_L035 and
NPO_COMPUTABLE_SCOPING.md (section 8). The recorded-pair data plumbing (NPN plan step 3) was not
started.

## 6. Validation that ran

Each scope's receipt, reservation, time log and stdout are in NPO_L0xx/; the table is in
NPO_ATTEMPTS.jsonl. 25 capped scopes were used, out of a budget of 30.

| Scope type | Labels |
|---|---|
| lean compiles (8G, `-M7000`, 180 s) | L001, L006, L007, L012, L017, L022 |
| the 16 GiB scope | L018 |
| native tool builds | L002, L004, L008–L010, L014, L019, L023 |
| native runs | L003, L005, L011, L013, L015, L016, L020, L024 |
| pinned walker | L021, L025 |

- **Caps.** Every 8G scope ran with MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0 and TasksMax 64,
  under a 180 s timeout. Lean was v4.32.0. Fewer than 6 capped scopes were populated at every
  reservation, and more than 54 GB of disk was free.
- **Swap and timeouts.** Swap was 0 everywhere. L003 timed out under MemoryHigh throttling. Its
  /usr/bin/time peak of 12.1 GB counts shared file pages; the cgroup cap held. The cause was a walker
  bug (no visited set), fixed before L004/L005.
- **Native tools.** These are NPO_DepsMain, NPO_Clone, NPO_Stmt and NPO_Noncomp. Each imports only
  Lean core at build time, loads the replayed oleans at run time, and runs under the same 8G cgroup.
  Native runs have no `-M` flag, the same as the pinned walker. NPO_Clone writes its olean with
  `writeModule` after every copy has passed `addDeclCore`. It never calls `addDeclWithoutChecking`.
- **Incident.** One uncapped command ran on the build host: `leanchecker --help`, outside any scope. It
  was meant as an independent replay check of NPO_CloneNov. I stopped it after about 2 minutes, killed
  the process, and confirmed that host memory was unaffected (8 GiB in use host-wide). No result was
  taken from it.
- **Reuse.** Nothing was reused as evidence except the L187 replayed objects on LEAN_PATH and the
  pinned walker binary. No full replay, Rust build, validator run or devnet access took place.

## 7. Assumptions and remaining work

**Assumptions.**

- None was discharged, added or removed.
- The trust rows of TAS_FinalB carry over unchanged; their statements do not involve the ids. The rows
  are RuntimeEntrypointAdmission, RuntimePersistence, S2TrustedSdkBorrow, TrustedStd, extraction and
  realization.
- The statement change is the host's id constants.

**Next deliverables.** Items 1 and 2 of the first round are done (section 8).

3. Row 5 non-vacuity (NPN plan): NPN_RecordedHost should be re-pointed to the `NPO_Nov.` host. That
   means re-cloning NPN_RecordedFrame/RecordedHost with this tool, which is mechanical, and switching to
   the 10 November recording (devnet NPC_TRANSACTIONS.json.xz). The executable triage then needs the
   computable host instance from section 5 before any R2 campaign.

**Owner-visible line:** host re-instantiated at the deployed program ids (10 November deployment) as a
model-fidelity correction; statement differs from TAS_FinalB only in the id constants.

Precisely: the kernel statement is TAS_FinalB's with six or seven host constants replaced by
re-instantiated copies. Those copies differ from the originals only by the verifier program id
(GqZz…) and the Pool/registry program ids (37hd…, 9pWw…). The registry id is the program 9pWwAcBg…,
not the account Hnn3D6DS…. One literal-byte lemma was restated. A 29 October instance exists alongside.


## 8. Continuation (lead instruction after the merge, budget 12 scopes; 10 used: NPO_L026 to NPO_L035)

### 8.1 Independent kernel replay with leanchecker

NPO_check.sh runs the toolchain's leanchecker (sha256 c7c51e29…). leanchecker uses
`Lean.Environment.replay` to replay every constant of the target module into the module's import
environment through the kernel. Each run was inside an 8G scope: MemoryHigh 6G, MemoryMax 8G, swap 0,
TasksMax 64, 180 s. The environment was `env -i PATH=<toolchain>/bin:/usr/bin:/bin LEAN_SYSROOT=<toolchain>
LEAN_PATH=out:L187 objs:L187 base_ref`, and the cwd was the log directory.

| Label | Command | Olean sha256 | Exit | Wall | Peak RSS (KiB) | Swap |
|---|---|---|---|---|---|---|
| NPO_L026 | `leanchecker -v NPO_CloneNov` | ccdf4987… | 0 | 9.35 s | 6,404,212 | 0 |
| NPO_L027 | `leanchecker -v NPO_CloneOct` | 40112a70… | 0 | 7.04 s | 6,422,700 | 0 |
| NPO_L030 | `leanchecker -v NPO_Teeth` (negative control) | d961d759… | 1 | 0.89 s | 451,264 | 0 |

The negative control was made in two steps. NPO_Teeth (built in L028, run in L029) writes a module
that imports only Init. It holds one valid theorem and `NPO_Teeth.bad : False := 0`. The kernel
rejected `bad` when it was added with checking, so it was then added with `addDeclWithoutChecking`.

leanchecker rejected that module: "while replaying declaration 'NPO_Teeth.bad': (kernel) declaration
type mismatch". So a pass of the replay is evidence. NPO_Teeth.olean was then deleted from out/, and
nothing imports it.

The first round's uncapped `leanchecker --help` (section 6) was, from the leanchecker source, a run
with no target. It resolves the current module through a lake manifest, finds none, takes the
anonymous name as a prefix, and so begins replaying every olean on the search path. That is why it did
not return.

### 8.2 Corrected restatement module (NPO_L031, the second authorised 16 GiB scope)

NPO_gen_final2.py fixes the three generator defects of NPO_L018:

1. `NNH8_RecorderFixed.fixedProgram` is renamed to its copy;
2. TAS_FinalB's open order is kept, so the AspisV8R19/FS opens come only before `deployed_charge`
   (the L018 "Ambiguous term" was `Bytes`: RSL vs AspisV8R19.DuplexFrames);
3. `ctx_same` is dropped.

It writes NPO_FinalB.lean (source sha256 af80a73d…). The v1 generator and the L018 file are retained
under NPO_gen_final.py and NPO_FinalBNov/Oct.lean for the L018 receipt; the v1 combined file was
overwritten by v2.

The compile ran with MemoryHigh 14G, MemoryMax 16G, swap 0, TasksMax 64, `lean -j1 -M15000
-DElab.async=false`, timeout 600. It finished in **exit 0**, 5.91 s, peak 6,871,932 KiB, swap 0, and
wrote out/NPO_FinalB.olean. The 10 PANIC blocks in the log are compiler noise from `abbrev`s over the
IR-less copies; there are no errors. `#print axioms` gives [propext, Classical.choice, Quot.sound] for
every declaration below.

| Name (10 November; the 29 October names carry the suffix Oct) | Definition or statement |
|---|---|
| `NPO_Program.verifier` | abbrev for `NPO_DeployedIds.verifierNov` |
| `NPO_Instances.D` | abbrev for `NPO_Nov.LIB_Instances.D`; `NPO_Instances.D_eq : D = NPO_DeployedIds.DNov` (rfl) |
| `NPO_InstancesOct.D_devnet` | `D = LIB_Deployed.devnet` (rfl) |
| `NPO_Run5bHost.S_host` | abbrev for `@NPO_Nov.AspisR1.NOC_Run5bHost.S_host` |
| `AspisR1.NPO_Run5bHostChecks.type_same` | the type is that of `NOC_Run5bHost.S_host` (rfl) |
| `AspisR1.NPO_Run5bHostChecks.args1_at` / `args2_at` | `args1 c = NNE_EntryArgs.args c.i.entry 3 NPO_Program.verifier c.i.data`, and the same for args2 with `c.j`, 7 (rfl) |
| `AspisR1.NPO_FinalB.deployed_splitB`, `fail_sub_rec`, `deployed_charge` | TAS_FinalB's run-7 text with the re-instantiated host constants, proved by the copies |
| `NPO_FinalB.deployed_splitB`, `deployed_charge`, `fail_sub_rec`, `deployed_outer` | the short aliases (`type_of%` of the restatements; `deployed_outer` = `NPO_Nov.AspisR1.NNH8_DeployedOuter`) |

### 8.3 Computable-host scoping (NPO_L032 to NPO_L035)

The note is NPO_COMPUTABLE_SCOPING.md; the data are NPO_L035/NPO_NONCOMPUTABLE.json and
NPO_NONCOMPUTABLE_BY_ROOT.json. NPO_L032 and NPO_L033 were a build and a refused run: `loadExts := true`
requires `enableInitializersExecution` first. NPO_L034 rebuilt the tool and NPO_L035 ran it.

In summary: 363 noncomputable constants are reachable from sdk, tx1Value, tx2Value, the TX1 producer
and I. None of them is noncomputable through `partial_fixpoint` or opaque externals; the extracted
Aeneas code is computable. There are 63 distinct leaves:

- about 34 `Classical.propDecidable` and 2 `Classical.decEq`. These are easy: the refinement is
  structural decidability, proved equal through the subsingleton property of `Decidable`.
- about 16 `Classical.choose`. Some are total-Result choices, which are easy: a match on `ok`, with
  injectivity giving equality. About 10 are existential selections that need uniqueness lemmas or a
  reviewed restatement; this is the hard class.
- 5 with no visible cause, needing compile probes.

The host sdk alone has 12 propDecidable leaves. My estimate is 30 to 70 scopes for a computable host
plus the executable run. I recommend the sdk refinements plus a 1-scope interpreter timing probe first.

### 8.4 Budget and assumptions

The first round used 25 scopes and this continuation used 10 of its 12. Nothing ran on the host
outside a capped scope during the continuation. No assumption was discharged, added or changed. The
statement change remains the host's id constants, as in section 3.

Target not yet established.
