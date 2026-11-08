# DGO_: O2 is true; host recipe

Target not yet established. Condition (4) is not proved here. Branch
codex/cx-dgo2-20261108 from research 82495476f4f.

## 1. Statement

O2 is quoted verbatim at the head of DGO_O2.lean, from DGP_HostDigest.lean
section 3. `RSL.Env` has exactly four fields: sha256, pda, clock and
reservation (`NNH_HostEnv.environment` builds it as `⟨sha, pda, clock, reserveOK
reservation⟩`). Under the three hypotheses, env and env' can therefore differ
only in sha256.

## 2. Decision: TRUE

The recorder reads env.sha256 through one route only: adapter.op43 =
`LIB_Env.hashv env`, which `NNH_Tx2SourceConfiguration.fill` installs inside
`NNH_CorrectConfiguration.residual`. Every reader of env was checked:

- `NNH_Tx2Configuration.select` reads env in two places.
  `NNH_Tx2ModelSlots.install` reaches `NNH_MRegistryOps.install` with
  op38 := `pda env`, which reads only env.pda, and the reserved field is set
  from env.reservation. `NND_DecoderSlots`, `NIJ_ActiveSlots` and
  `NHY_RegistrySlots` preserve op43 by their own rfl theorems.
  `NGL_CheckpointModel`, `NNH_LaneModel` and `NNH_AdapterStdCorrect` do not
  take env.
- `IDa_Deployed.deployedConfiguration`, `FIq_Install`, `FIp_Install`, `FIo`/`Rc5`
  and `DrvC_Installation.sdk` never set or read op43. Tx2I_Install sets only
  op11, and AspisS6CurrentFirstInstallation sets op10 plus codecs. Boundaries
  are the fixed `IDa_Deployed.boundaries r`.
- Inside the recorder, the only reader of op43 in `AdapterRwModel.lean` is
  `SolanaDigest.Insts.Aspis_coreDigestDigest32` (line 643). Only the op10 call in
  `first_decoded` (S2W_Outer line 194) and the op11 call (line 733) use it, as
  the dictionary argument. The trace never performs `Call.op43`. The observer
  `Hiq_ByteSelection.select` uses OwnedAccount.data, validate_asq8 and op22.
- `GExq_ChildCode.execute` intercepts op10 and op11. The dictionary reaches
  `SdkD_PrepareSource.code` and `GExq_BatchSource.current`/`stage`. There,
  `SdkD_PrepareLower.lower` drops it at digest nodes. The source's own
  irrelevance theorems already establish that its digest field is unused at
  the program level: `S1PrepareCode.dictionary_irrelevant` (arbitrary base and
  B; claim law discharged by `claimPublic_digest_irrelevant`), and
  `SdkC_BatchSource.erasure` / `Port9OR_Batch.values_source` for arbitrary D and E.
  The two dictionaries share coremarkerCopyInst (its clone is op42 :=
  `fun _ => .ok ()`).

No counterexample exists, so the top statement needs no change and nothing is
referred to the owner. The teeth vector `leaky_differs` shows that the absence of
`Call.op43` in the trace is load-bearing. A trace that issued op43 and branched
on its reply would refute O2.

## 3. Proof status

DGO_O2.lean is the compiled proof over faithful stand-ins: exit 0 under lean
4.32.0 and 4.35.0, with standard axioms only (DGO_O2_STDOUT.txt). It uses no
sorry, no axiom and no premise beyond O2's three hypotheses, and it does not
restrict the adversary or hashv. The host instantiation below is NOT compiled:
its imports exist only on the build host.

## 4. Host recipe (one focused scope per item, in order)

Every scope runs as `systemd-run --scope -p MemoryHigh=6G -p MemoryMax=8G
-p MemorySwapMax=0 lake env lean -M7000 <file>` in the NNH_ pinned workspace.
The new module prefix is DGO_. The transcription column names the mirror lemma.

| # | Host lemma (real names) | Proof | Mirror |
|---|---|---|---|
| 1 | `withDigest c o := {c with adapter := {c.adapter with op43 := o}}`; `split`: `FIp_Install.configuration err (deployedConfiguration (select (residual m0 env) env) err r) r = withDigest (… env' …) (fun _ p => LIB_Env.hashv env p)` | `obtain ⟨s,p,k,v⟩ := env; obtain … := env'; dsimp only at hp hc hr; subst hp hc hr; rfl` | split |
| 2 | `DrvC_Installation.sdk (withDigest c o) = {DrvC_Installation.sdk c with op43 := o}` | rfl | sdk_withDigest |
| 3 | `Hiq_ByteSelection.select {S with op43 := o} id out = Hiq_ByteSelection.select S id out` | `unfold select account public2; rfl` (op43 is absent from these AdapterRw helpers) | observe_op43 |
| 4 | `CallSim`/`Sim` over `S2W_Trace.Call`/`Code`; `lowerN_sim` for `GExq_OuterLower.lower` | transcribe the mirror. `CallSim.same` needs `NotDigest` (not `.op43`); variants op10 and op11 have equal `coremarkerCopyInst` | Sim, lowerN_sim |
| 5 | `Sim (S2W_Outer.stage1_owned {S with op43 := o} traceEffects …) (stage1_owned S traceEffects …)` and the same for stage2_owned | GExq_OuterGoodStage1 loop with sim_bind/sim_lift/sim_perform; separate lemma for `first_decoded` (local irreducible). Equal non-digest helper steps close by rfl (op43-free) | stage1_sim |
| 6 | `DSim` over `PreparedHashCode.Code`; `lowerP_dsim`; `DSim (S1PrepareCode.prepare base R B D1 …) (… D2 …)` | port the dictionary_irrelevant family (S1CurrentPrepareCausalV1, S1ClosedPreparationCausalProgramV1, S1PreparedOracle{Dictionary,ScalarQueries,Complete}IrrelevanceV1, S1SemanticCodeDictionaryV1), replacing oracleProgram_bind_congr by dsim_bind, oracleProgram_digest by DSim.digest, and the claim step by claimPublic_digest_irrelevant | lowerP_dsim, prepare_dsim |
| 7 | `GExq_BatchSource.current D1 … = current D2 …` and stage, through Port9OR_Batch.values, Port9OR_BatchTree.code, BatchLoop and BatchStep.body | unfold each level; the dictionaries share copy | batch_eq |
| 8 | `GExq_FirstCode.code … (toDigest D1) … = … (toDigest D2) …` and `GExq_SecondCode.code … D1 … = … D2 …` | rw by 6 and 7 | firstCode_eq |
| 9 | `child_sim`: `GExq_ChildCode.execute` at withDigest = at c on CallSim | same: `cases x <;> rfl` (invoke off op43); op10/op11: by 8 | child_sim |
| 10 | `ART_PartialAccount.account (withDigest c o) hashv copy alloc id a = account c …`; recorder; `DGP_HostDigest.O2` | unfold firstSyntax/secondSyntax, GExq_InstalledWrapper, GExq_Caller.first/second; rw by 2, 4, 5 and 9; `NNH_RecordedCharge.recorder` unfolds to Hiq_RecordedJoint.program of bounded account and ARQ_Observer.select at the FIp configuration; rw by 1 and 3 | account_withDigest, o2 |

Expected cost: items 5 and 6 are the long ones; the oracleProgram family they
port already compiles at this shape. Items 1-3 and 9 use only small
structure-projection rfl. No numeral or recurrence is reduced.
Next consumer: `NNH_RecordedCharge.bound` at a fixed base, transported by
O1 (`NNH_DigestSyntaxTransport.o1`, archive corrected but not recompiled) and
this O2, then the condition (4) pointwise inclusion under the 2026-11-08 owner
decision.
