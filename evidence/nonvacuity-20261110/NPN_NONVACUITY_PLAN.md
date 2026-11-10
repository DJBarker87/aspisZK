# NPN_ non-vacuity plan: gate row 5 of SOUNDNESS-CLAIM-DRAFT-20261108

Stream A scoping job, 2026-11-10. Worktree cx-integrate (branch codex/cx-integrate-20261107), after
`git merge --no-edit research` (fast-forward to 8f981cf190d). Host workspace
/home/dombarker/project-offloads/codex-cx-nonvac-20261110 (LEAN_PATH: own out/, then the L187 replayed
objs/ and base_ref/ by reference; nothing copied). No merged module was edited. Target not yet established.

## 0. Answer in one paragraph

No route gives a `Runs` inhabitant from a recorded pair cheaply. The frame half is cheap and is now
proved: GameFrame, both RuntimeEntrypointAdmission rows, RuntimePersistence, QueriesF, Out2 and the
context identities, all at a world built from recorded images (section 5, two compiled modules).
Three fields remain: `ok1` with `out1`, `ok2`, and `trace`. They need a Lean proof that the installed
model accepts the recorded bytes. R4 cannot supply that, because nothing in Lean connects the physical
ELF execution to `stage1_owned` or `I.entry`. Its hypothesis would be the residual itself (section 3).
I recommend R4 for the physical frame and R2 (per-call evaluation, with H chosen as the table of the
run's recorded queries) for acceptance. Before any R2 work starts, finding F1 must be resolved: the
host theorem is pinned to identifiers that no recorded run used. My estimate for the whole witness is
roughly 200 to 600 capped scopes. A 2-to-4-scope executable triage of the Lean model on the recorded
bytes should gate that campaign.

## 1. What `Runs` asks for at the host

`RSL.TASB.Runs S I c` (TAS_TopB) has six fields. Here S is `NOC_Run5bHost.S_host L0 copy std`, I is
`NNH_Run6Installed.implementation allocation217 allocation234 ch NNG_Candidate344.allocation alloc2`,
and c is `ctxB (NNH8_Exec.exec L0 copy std) fx w H`. deployed_splitB also needs inhabitants of `L0`,
`borrow`, `copy`, `std` and `queries`.

| Field | Unfolds to (NNH8_NonVacuity, NOC_Run5bHost) | Kind of fact | Status |
|---|---|---|---|
| `borrow`, `std` | `S2TrustedSdkBorrow L0`, `TrustedStd copy` | consistency witnesses `S2Trust.model_satisfies`, `S2W_TrustedStd.specification_satisfies` | **proved** (instantiated, NPN_RecordedHost) |
| `queries` | `∀ J K, (ARW_Induced.issued … (normalize fx.a) K).length ≤ Q0+Q1` | adversary bookkeeping | **proved** for the zero-query recorded adversary, Q0 = Q1 = 0 |
| `frame` | CPG game (a)-(c) plus the non-trace part of (d), ∧ `retained` (admission1, admission2, RuntimePersistence) | physical facts of the recording | **proved** from recording facts (`same`, `key`, `inj1`, `inj2`) |
| `out2` | `True` | none | **proved** |
| `ok1`, `out1` | `I.entry (args1 c) (state1 c) (env1 c)` returns `ok ()`, and its write events are the carrier image of `saved` | **model evaluation** of TX1: dispatch, stage1 windows, then `NNG_TotalProducer345.producer` | residual |
| `ok2` | `I.entry (args2 c) …` returns `ok ()` | **model evaluation** of TX2 stage 2 (241 with 233/234/242/064) | residual |
| `trace` | `NNH_RuntimeTrace.Trace` for TX1's post-copy actions and TX2's actions: each `.invoke` is associated with `I.entry` at the RSL images, and each other action is the recorded Pool or runtime action | the invoke step is model evaluation; the other steps are recorded data | residual |

## 2. Findings

**F1 (blocks every recorded-run witness as stated; lead or owner decision).** The host theorem fixes
two kinds of identifier, and neither matches the recorded runs.

- The verifier program id is `CPH_Program.verifier` = 7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue. That is
  the July 2026 profile23 V7 devnet program (README; DEPLOYMENT-SOL-RECOVERY-POLICY). S_host passes it
  as `args1/args2` program and as `data.program`, and it appears in the QueriesF form.
- The Pool and registry ids are `LIB_Instances.D = LIB_Deployed.deployed = ids false`. Those are the
  default-image placeholders: pool 0x41^32 = 5PjDJaGf…, registry 0x44^32 = 5bV6jUfh….

Every R1 execution ever recorded ran the devnet image 63ad3e9c at verifier CSnhzGdH…, with pool BmsNik…
and registry 9pWw…. That covers NPC_ local and NDZ devnet; the devnet ids are `LIB_Deployed.devnet`.
NPN_RECORDING_FACTS.json gives the consequences:

- TX1's `verifierCheckpoint ck program_id` requires the checkpoint owner (CSnhzGdH… in the record) to
  equal 7Q2n…, so the model rejects TX1 as recorded.
- TX2:234 compares the pool and registry program ids with D, and the entry's `verifier_program`
  (bytes at offset 40 of CTBkdziF…) with the verifier program id, so the model rejects TX2 as recorded.

The TX1 proof, statement and checkpoint bytes contain none of the three ids. A renaming therefore
leaves every TX1 hash input unchanged. In TX2 the ids occur in the master (offset 216), the registry
(offset 120), the entry (offset 40) and the Pool instruction data (offset 72).

Options:

- (a) Re-instantiate the host at `LIB_Deployed.devnet` and program CSnhzGdH…. This is a statement
  change: the theorem would then describe the deployed image. It is probably mechanical if the cone is
  parametric in D and the program id. Preflight: 2 to 4 scopes.
- (b) Build the witness from the recorded pair under a consistent renaming of the three ids. This is
  data-only, about 2 scopes. It is honest only if it is reported as "the recorded run up to renaming",
  and TX2 renaming is valid only if none of the renamed bytes is hashed or authenticated in a way the
  renaming breaks. That needs checking.
- (c) Make a fresh local-validator recording with the default image f8c0ec72 loaded at the model's
  addresses. This is about 4 h of validator time. It needs a Pool build carrying the default ids and
  new proofs.

I recommend (a), because the theorem should name the deployed image whatever happens to row 5. Until
then, (b) is admissible only for a witness explicitly labelled "renamed".

**F2 (R3 as stated is infeasible).** Aeneas `loop` is `partial_fixpoint` (Aeneas/Std/Primitives.lean:280).
That makes it `Lean.Order.fix` over the flat-order CCPO, whose supremum is classical, so the kernel
cannot reduce any extracted loop by `decide` or `rfl`. Only the unfolding equation `loop.eq_1` can step
it, by rewriting. Separately, `Slice` indexing is linear traversal of a `List` in the kernel. The
verifier indexes the 57,607-byte proof thousands of times, which puts whole-run kernel evaluation in
the 10^8 to 10^9 step range: far past -M7000, and exactly what AGENTS rule 2 forbids by default.

**F3 (precedent).** The joint-fixture campaign (JFx_ … JHn_, evidence/joint-fixture*-202610{26,27,28}
and fixture-tx2*, 2026-10-26 to 28) attempted this route on the RPx-era model.

- After about 35 rounds of up to 100 capped compiles, JHn_TX1Frontier proves first-wrapper acceptance
  of a retained 57,607-byte fixture through `AspisR1CurrentCaller.verifier.candidate.tx1`. That is the
  same extracted function the R1 host reaches in `NOC_Stage1Forward.fdLemma`, but at a different ops
  dictionary.
- That acceptance is conditional only on `JHe_SHARealization`: 453 concrete SHA-256 tree equations.
- The final joint application exceeded -M7000 at import and was never compiled.
- 26 TX2 rounds (JHf/JHj) did not reach `accepted2`.

At the R1 host, H is a theorem binder, so the SHA class disappears: a table H makes each `H q = d` a
lookup. Whether the JHx arithmetic, field-range and writer lemmas port depends on two checks: whether
`installed` and `NNH_Run5bCurrentShape.current (NOC_Tx1Forward.M c) …` agree on the slots the
accepted path reaches, and whether the cached JHx objects are coherent with the L187 closure. Neither
has been checked.

**F4 (direction of the Ok clauses).** `NOC_Stage1Iff.iff345` is an iff between two Lean models:
`stage1_owned (sdk c)` and `NNH_ReturnsBundle.tx1Value`. `NOC_Stage1Forward.ok345` (reference ⇒ model)
is what A1 uses. Neither side is the physical ELF, and no Lean object relates them; that link is the
extraction and realization trust of sections 4.4 and 4.6. `ok1` is also stated at `I.entry`, the RSL
implementation built from `NNG_TotalProducer345.producer`, not at `stage1_owned`. `NNG_TotalProducer345.interpretation`
says that implementation equals `NNG_Phases345.run` over the same LIB values that `tx1Value` sequences.

**F5 (memory).** Importing TAS_FinalB costs 7.0 GB of the 8 GB cap (L187: NNH8_Statements at
7,011,600 KiB). NPN_RecordedHost imports NNH8_Exec and NNH_Run6Installed at 6.85 GB. The final corollary
through deployed_splitB will sit at the cap edge and may need the 16 GiB aggregation scope.

## 3. Route assessment

### R4: accept-trace replay (assessed first)

- **Statement.**
  `∀ r, RecordingFacts r → Runs S I (ctxB X (fixed r …) (world r …) H_r)`, where RecordingFacts holds
  only facts about recorded data.
- **What R4 gives.** The frame, both admissions, persistence and the non-invoke trace steps are physical
  facts. They are now constructed and proved from the images, which is exactly TAS_WIRING item 8's
  "recorded-trace facts, not False", and in addition the trust rows are shown satisfiable at a recorded
  world.
- **What R4 cannot give.** It cannot give `ok1`, `out1`, `ok2` or the `.invoke` trace step. The only way
  native acceptance enters Lean is the bare equation
  `stage1_owned (sdk c) program xs data = .ok (.Ok saved)`, or its `I.entry` form, taken as a hypothesis
  at the recorded inputs. That is the residual itself. It is a per-input instance of the extraction
  trust, not a statement about the recording.
- **Why that does not count for row 5.** A witness built on that hypothesis cannot detect a vacuous
  model. NOC_PrepareDiv's old seed, with op1 := `.div`, never accepted TX1, and R4 would have
  "witnessed" it all the same.
- **Recommendation.** Use R4 for the physical half. TAS_WIRING item 8 is satisfied by NNH8_NonVacuity
  plus NPN_. Gate row 5's "Runs inhabitant from an actual accepted pair" is not.
- **Unproved on this route.** The native-trace-to-model correspondence (extraction, D188, R22, ELF
  realization).
- **Scope.** Done: 4 scopes, 2 of them repairs.

### R1: completeness

- **Statement.**
  `∀ st w ρ, HonestRel st w → tx1Value (args (prove st w ρ)) env_H = .ok (checkpoint …)` for all H,
  plus a TX2 analogue, then transported by A1/A2.
- **Inputs.** A Lean prover model. The soundness closure has none; the privacy side is only
  regenerating its prover extraction (claim draft item 18). It also needs the spend witness, which the
  recording does not contain and is private.
- **Obstacle.** This is full STARK/FRI completeness plus the transcript, Merkle and terminal layers,
  over an extracted prover.
- **Scope.** More than 500 scopes. It would also give "some honest run", not the recorded one.
  Not recommended.

### R3: certified evaluator

- **Statement.** `E = model` on the domain, with `decide (E recorded = accept)` evaluated in the kernel.
- **Obstacle.** F2. The fix would be a generated fuel-indexed copy of every cone loop, a generic
  "fuel approximant agrees with partial_fixpoint when it is not div" lemma (provable once), and
  per-function monotonicity. The kernel cost of List-backed slices on 58 KB remains.
- **Scope.** More than 150 scopes, and the kernel run is still likely infeasible. Use it only for
  structural leaves, for example `LIBC_CanonicalScan.good`, which is `List.all` over NKL checks.

### R2: symbolic per-call evaluation (recommended for acceptance)

- **Statement.** The 10 TX1 library-call equalities at the recorded arguments (section 4, L3). Each is
  proved by generated, named per-iteration or per-cell lemmas (AGENTS rule 3), never by whole-term
  normalization. Then the TX2 analogue for 241 and its children.
- **Choice of H.** H := the table of the run's queries, with digests recomputed offline. The recording
  has no syscall replies. The query list comes from re-executing the frozen verifier natively with a
  logging hash, and each digest is recomputed with hashlib. The table agrees with SHA-256 on every
  query the run makes; that is checked offline. Because `deployed_splitB` holds for every H, this is
  legitimate.
- **Inputs from the recording, all present.** TX1: the proof carrier (58,295 bytes; the verifier reads
  57,607 after the 688-byte prefix), the 1,880-byte statement, the 1,768-byte checkpoint pre and post
  images, instruction data `[3,10]`, and account metas. TX2: the 13 images, the verifier-CPI account
  order from innerInstructions (`[proof, master, …, registry, entry, checkpoint]`, checkpoint at 6), and
  its instruction data. The Clock slot is present. Absent: PDA and Clock syscall replies. `fx.pda` and
  `fx.clock` are universal, so they are chosen as the recorded program-derived addresses, recomputed
  offline.
- **Obstacle.** Size (F3), plus F1.
- **Scope.** See section 6.

## 4. Exact statement and the first three lemmas

Target theorem (to be generated after F1):

```
theorem AspisR1.NPN_Witness.runs :
  RSL.TASB.ExecB.QueriesF NPN_RecordedHost.X NPN_Witness.fx ∧
  RSL.TASB.Runs NPN_RecordedHost.S
    (AspisR1.NNH_Run6Installed.implementation NPN_Witness.allocation217 NPN_Witness.allocation234
      NPN_Witness.ch AspisR1.NNG_Candidate344.allocation NPN_Witness.alloc2)
    (RSL.TASB.ctxB NPN_RecordedHost.X NPN_Witness.fx NPN_Witness.w NPN_Witness.H)

theorem AspisR1.NPN_Witness.nonvacuous :=   -- the deployed_splitB conclusion at these closed binders
  AspisR1.TAS_FinalB.deployed_splitB NPN_RecordedHost.L0 NPN_RecordedHost.borrow NPN_RecordedHost.copy
    NPN_RecordedHost.std NPN_Witness.allocation217 NPN_Witness.allocation234 NPN_Witness.ch
    NPN_Witness.alloc2 NPN_Witness.fx NPN_Witness.w NPN_Witness.H runs.1 runs.2
```

Here `fx := NPN_RecordedHost.fixed r data1 data2 slot base` and `w := NPN_RecordedHost.world r post1 post2`.
`r`, `data1`, `data2`, `slot`, `base` and `H` are closed literals generated from NPC_LOCAL_TRANSACTIONS
records 35/36, written as chunked data modules on the JFx_Data* pattern. The allocation streams are
all-success. The binders keep their universal status in the theorems; this is only an instance.
`a` is the recorded pair as a constant adversary, which is admissible for a witness, while condition
(4) forbids it in the theorem itself.

- **L1 (compiled: NPN_RecordedFrame, NPN_L002).** Defines the recorded world: `Recorded`, `layoutOf`,
  `obs`, `e1`, `e2`. Global cell `2k` holds data, `2k+1` lamports, Tx = Bool. It proves:
  - field-level correspondence: key, owner, lamports, flags and rent epoch are `rfl`; the data buffer
    is the recorded data for every funded account;
  - `frame`: game (a)-(c) and the non-trace part of (d);
  - `admission`: RuntimeEntrypointAdmission at `S2Trust.model` with world := the entry heap, given key
    injectivity on the n accounts;
  - `persistence`: TwoTransactionLaw.
- **L2 (compiled: NPN_RecordedHost, NPN_L004).** At S_host it gives:
  - `borrow`, `std`, the zero-query `adversary` and `fixed`;
  - `ctx_fields`: the context's pair is the recorded pair, at every H;
  - `queries`; `frame`, the full host GameFrame including `retained`; `out2`;
  - `runs_of_residual`: Runs follows from `trace`, `ok1`, `out1` and `ok2`. These four hypotheses are
    the exact residual of row 5.
- **L3 (next): `NPN_Tx1Transport.ok1_out1_of_calls`.** This is symbolic and evaluates nothing. Given
  the ten call equalities at `a1 := ⟨key verifier, accounts e1, [3,10]⟩` and `env := envOf c`:
  - `LIBC_ParseShape.value proof env = .ok ()`, `LIBC_CanonicalScan.value proof env = .ok ()`;
  - `NNH_PrepareReturns.value … = (.ok p, g)`, `LIBC_AccNew.value env = .ok acc`;
  - `LIBC_BatchMerkle.value (proof,p,folded,0) env = .ok _`, `LIBC_Geometry.value … = .ok geo`;
  - `LIBC_WeightsNew.value acc env = .ok pending`, `LIBC_QueryLoop.value … = .ok q`;
  - `LIBC_Finish.value … = acc2`, `LIBC_Checkpoint.value … = bytes saved`;
  - the TX1_345 body checks: distinct keys, readonly carriers, checkpoint owner/length/zero, decode and
    validate statement, candidate prefix and S2 tag.

  It derives `ok1` and `out1` at `I.entry`. The route rewrites through `NVR_Dispatch.entry`/`process`
  (`[3,10]` is a stage-1 route), the `NMV_ConcreteWindows.stage1` windows with all-true allocation, and
  `NNG_TotalProducer345.interpretation` / `NNG_Phases345.run`. The same equalities give `tx1Value = .ok`,
  so `ok345` also yields `stage1_owned = .ok`, which is useful as a cross-check. Estimate: 6 to 12
  scopes. Its hypotheses are the R2 evaluation targets.

## 5. Validation that ran

| Label | Module | Exit | Wall | Peak RSS | Swap | Notes |
|---|---|---|---|---|---|---|
| NPN_L001 | NPN_RecordedFrame | 1 | 2.22 s | 5,295,220 KiB | 0 | `meta` is a keyword (parse error); rejected |
| NPN_L002 | NPN_RecordedFrame (sha256 70d0c2c1…) | 0 | 2.46 s | 5,321,100 KiB | 0 | axioms: propext, Classical.choice, Quot.sound |
| NPN_L003 | NPN_RecordedHost | 1 | 3.47 s | 6,805,652 KiB | 0 | `queries`: split under `have`; rejected |
| NPN_L004 | NPN_RecordedHost (sha256 cdaa9043…) | 0 | 3.34 s | 6,852,752 KiB | 0 | axioms standard for all 7 roots; no sorry |

Every scope ran with MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0 and TasksMax 64, using
`lean -j1 -M7000 -DElab.async=false`, timeout 180 s, Lean v4.32.0. Each reservation was admitted with
fewer than 6 capped scopes and more than 58 GB free. The receipts are in NPN_L00x/. Source revision:
cx-integrate at 8f981cf190d plus this commit. NPN_RECORDING_FACTS.json is produced by
NPN_recording_facts.py from the decompressed recording (sha256 3b8af292…, the value in
NPC_LOCAL_RESULT). It records:

- the TX1 account list, and the TX2 verifier-CPI account list with the checkpoint at position 6;
- shared TX1-post and TX2-pre images, equal for all four shared accounts (faithfulness item F-a below);
- the isolation windows, the CU, the checkpoint owner, the model's ids against the recorded ids, and
  where the ids occur in the data.

Nothing was reused as evidence except the L187 replayed objects on LEAN_PATH. No TAS_FinalB import,
full replay, Rust or validator run took place.

## 6. Remaining obligations and estimate

1. **F1 decision**, then its preflight: 2 to 4 scopes.
2. **Triage gate**, labelled an executable model check and not a proof. Run a compiled `#eval` of
   `tx1Value`/`tx2Value` and of `I.entry` on the recorded bytes, with H := a Lean SHA-256 (JFp_SHA256
   exists), to confirm the Lean model accepts this run before spending R2 scopes. Whether
   `noncomputable section` definitions compile is part of the triage. 2 to 4 scopes.
3. **Data generator and literal modules.** Images, metas, the instruction data, the Clock slot, H table
   entries and the pda table. Its `--check` mode reads the hashes back against the recording.
   3 to 6 scopes.
4. **Faithfulness obligations.** These are offline checks against the recording, receipted; they are
   not Lean theorems.
   - F-a: post1 equals pre2 on the shared accounts (done).
   - F-b: nothing touched the shared accounts between slots 1575 and 1607. This needs the retained
     6.5 GB ledger or the NPC_REPLAY inputs; the isolation check covers each transaction's own window
     only.
   - F-c: the H table agrees with SHA-256 on every query.
   - F-d: the input-region `base`/`provenance` values follow the SBF serialization layout.
   - F-e: the TX2 non-invoke actions (system create, Pool writes, fee debits) reproduce the recorded
     post-images.
5. **L3 TX1 transport:** 6 to 12 scopes.
6. **TX1 per-call evaluation:**
   - parse/scan: 2 to 6 scopes;
   - accNew/weights/geometry: 3 to 6;
   - prepare (transcript, public, semantic rounds, claims, terminal): 40 to 120;
   - batch Merkle, 22 queries at H := table: 30 to 80;
   - query loop: 40 to 120;
   - finish/checkpoint writer: 10 to 25.

   That is about 130 to 360 in total. JHx shows the variance is large.
7. **TX2:** the stage-2 evaluation (241 with 233/234/242/064), the `.invoke` trace step at I.entry,
   and the Pool-action trace: 60 to 200 scopes.
8. **Final assembly:** `NPN_Witness.runs` and `nonvacuous`, at the TAS_FinalB import edge (F5).
   2 to 5 scopes, possibly in the 16 GiB scope.

The total is roughly 200 to 600 capped scopes. If the R1 host shares the JHx candidate-tx1 path on
the reached slots and the JHx objects can be rebuilt coherently, the TX1 items could drop to
perhaps 60 to 150.

## 7. Before/after and trust

No theorem statement, ledger row, trust row or merged module changed. The new modules add no
hypothesis to any credited theorem. At a recorded world, the trust rows RuntimeEntrypointAdmission
and RuntimePersistence are now proved facts rather than assumptions, which shows they are
satisfiable. They remain trust rows of the theorem. S2TrustedSdkBorrow and TrustedStd are
instantiated by their existing consistency witnesses (identity library, specification copy). That
makes the witness non-vacuous for those binders only; it says nothing about production SDK or std
behaviour. Gate row 5 stays PARTIAL. What changed is that the residual is now an exact compiled
statement: the four hypotheses of `runs_of_residual`.

Target not yet established.
