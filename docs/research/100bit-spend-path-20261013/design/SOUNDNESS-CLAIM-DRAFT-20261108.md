# Soundness claim for the R1 verifier spend path (draft)

**Status: DRAFT. Target not yet established.** This document is the text Stream A intends to publish when the soundness target is met. Until every item in section 6 has evidence, the word "established" must not be applied to anything in it, and every heading below is read as "intended claim", not as a result. The draft changes no proof, ledger row, trust row, contract text or frozen source.

Basis for this draft: `research` at def3eee1fa1. Sources read:

- design/SECURITY-CONTRACT-20261021.md and its amendments of 2026-10-26, 2026-10-27 (three), 2026-10-28 (fourth, fifth, standing delegation) and 2026-11-09;
- C3-BIN-20261021.md, rulings (bc), (bk) with its addendum, (bm) to (bt), the owner decisions of 2026-11-07 (split top, option B with Realizes, binding conditions, RZ-STATE) and of 2026-11-08 (condition (4) by pointwise inclusion);
- evidence/top-assembly-20261107 (TAS_TopB.lean, TAS_TopB_NNE.lean, TAS_Interfaces.lean, TAS_G0_BRIEF.md), evidence/top-form-20261107 (TFM_TopExact.lean, TFM_REPORT.md), evidence/event-b-20261107 (EVB_REPORT.md, EVB_range.py), evidence/int-plan-20261107 (INP_REPORT.md), evidence/digest-p2-20261108 (DGP_DECISION.md);
- evidence/ledger27-20261111 (NNK_HANDOFF.md, NNK_REMAINING.md, NNK_TOP_COMPOSITION.json, NNK_TRUST_ADDITIONS.json, NNK_LEDGER_DELTA.json, NNK_K086.json, NNK_LEDGER.json.xz);
- design/TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md;
- evidence/replay-deployed2-20261027/RPx_Deployed.lean (the adopted headline) and lean/F3T_Numeric.lean, lean/F3U_Range.lean, lean/F3U_RangeMaximal.lean, lean/F3U_RangeEdges.lean.

Where this draft reconstructs a statement that has not been compiled, it says so. The published version must replace every reconstruction with the kernel statement printed from the compiled theorem.

## 0. Current position in one paragraph

*Updated 2026-11-09 after NNH_ run 7 (G0 FINAL), merged to `research` at 1133ee43a9f.* Ledger30 (NNN_) records 599 CLOSED, 0 QUALIFIED and 0 OPEN spend-path rows. The host top is assembled unconditionally at the corrected host `AspisR1.NOC_Run5bHost.S_host`. `AspisR1.TAS_FinalB.deployed_splitB` and `AspisR1.TAS_FinalB.deployed_charge` compile in `TAS_G0_COMBINED_IMPORT` with every interface field a delivered closed term. The three fields that were missing in run 6 are now filled: a1 := `AspisR1.NOQ_FinalCombined.field`, a2 := `AspisR1.NOF_A2FieldCorrected.field` and sp.rest := `AspisR1.NNH8_Rest.assemble`. TAS_G0_MISSING.json is empty. Condition (4) is proved under the section-1 rule as amended by ruling (bu) (section 7, item 12). G0 gate rows 1 to 4 of section 6 have their artifacts. Row 5 (non-vacuity) is partial, and release gates 5 to 16 are open. Extraction provenance (note (bk)) is still an unresolved release blocker.

## 1. The theorem as it will stand

### 1.1 Precise prose

Fix the frozen verifier implementation (crates/, programs/r1-cost-probe and Cargo.lock at 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387) in the installed configuration `IDa_Deployed.deployedConfiguration missing indexError reservation`, with the owned TX1 and TX2 stage bodies taken at their AdapterRw models. Model SHA-256, as invoked through the runtime's hash syscall, as a uniformly random function H : Bytes → State. Let `a` be an arbitrary two-phase adaptive adversary (`SCE_Experiment.Adversary Bool`) and let `a⊤` be `a` with both of its allocator-state outputs replaced by `true`. Suppose that, for every oracle H, the digest queries issued by `a⊤` across both reached phases (`ARW_Induced.issued`, counting duplicates and every call issued before a rejection) number at most Q = Q0 + Q1.

For each H, let the deployed pair be what `a⊤` actually outputs at H: `⟨e1, data1, true⟩ := (eval H a⊤.first).2` and `⟨e2, data2, slot, true⟩ := (eval H (a⊤.second ⟨e1, data1, true⟩ saved post1 true)).2`. Suppose further that these two entries are executed by the Solana runtime as the approved two-transaction game: consecutive executions on one bank lineage, the same physical checkpoint account named by both with no intervening touch, TX1's parent status success, and the recorded checkpoint actions equal to the physical runtime actions (`Runs`: `frame`, `trace`, `ok1`, `out1`, `ok2`, `out2`), under the retained runtime, SDK and standard-library hypotheses.

Then three things hold (the first is H-free; the second and third hold at every H):

1. the numeric conjunct C5num of the adopted headline: `failureModel runtime ≤ total(Q)`, where `failureModel` is an average over H (bound-audit finding 3: it is not a per-H statement); if Q ≤ maxQueries then `failureModel runtime ≤ (Q+1)·2^-100`; and if Q = 0 then `failureModel runtime < 2^-100` with the exact margin;
2. the other conjuncts of `AspisR1.RPx_Deployed.deployed` except conjunct 4, unchanged (`Rest`: P6 boundary, driver and SDK equalities, the three Claims, copy facts, Rc2 events, CPH protection, trace and recorder facts, S6N installation);
3. either conjunct 4 holds with its internal bad event re-targeted to E_rec (`OutcomeRec`), or E_rec holds at H.

E_rec is the collision event already charged inside `failureModel`: `BinRawByteCollisionTargets.event` at Q + 2965 recorded reads on the adversary's own capped account run with the output-dependent selector `ARQ_Observer.select`.

Averaged over all H, with no conditioning and no H excluded, the per-attempt failure indicator `max r 1_{Runs ∧ ¬OutcomeRec}` has mean at most total(Q), with E_rec charged once. [Bound audit, 2026-11-08, finding 4: "charged once" is established in compiled Lean only for `failureModel`; for this per-attempt event including OutcomeRec it rests on the stand-in `RSL.EVB.no_second_charge` and a host theorem that is not yet compiled (section 1.2.2, G0 final). It is stated here as the target, not as a fact.] Here `r` is the per-world loss whose mean is `failureModel`, namely the extractor-failure mass of the accepted run (`RawRecordedOracleExtractionMassBin.failureMass`: the run is accepted and `RawRecordedPublicSpendExtractorBin.extract` returns `none`) plus the query-scan term.

### 1.2 Lean form

#### 1.2.1 Compiled stand-in (exists)

The stand-in stack compiles locally with `#print axioms` showing only `propext`, `Classical.choice` and `Quot.sound` (TAS_AXIOMS_OUTPUT.txt, TFM_AXIOMS_OUTPUT.txt, EVB_AXIOMS_OUTPUT.txt; rev2 local compile in top-assembly-20261107/rev2/REV2_LOCAL_COMPILE.tsv). In it, every headline object is a field of `Sig`, `RecSig` or `ExecB`, never an `axiom` or `opaque`. These are the two theorems the host will instantiate, quoted from TAS_TopB_NNE.lean and TAS_TopB.lean:

```lean
theorem RSL.TASB.top_splitB_physical {S : Sig} {R : RecSig S}
    (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_Roots L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (nmn : NMN_Root L V0 VL I)
    (g1a : NNC_G1a S L V0 VL I) (rs : RecSelect S R) (hb : HeadlineB S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (count1 : ∀ c, (S.args1 c).accounts.length = 3)
    (count2 : ∀ c, (S.args2 c).accounts.length = 7)
    (X : ExecB S R) (fx : X.Fixed) (w : X.World) (H : X.Oracle)
    (queries : X.QueriesF fx) (run : Runs S I (ctxB X fx w H)) :
    S.Bound (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∧
      sp.Rest (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∧
      (hb.OutcomeRec (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∨
        X.ERec fx H)

theorem RSL.TASB.deployed_charge … (X : ExecB S R) (Ex : Expect X.Oracle) (fx : X.Fixed)
    (wOf : X.Oracle → X.World) (queries : X.QueriesF fx)
    (r m : X.Oracle → Rat) (T : Rat)
    (hm : ∀ H, 0 ≤ m H)
    (each : ∀ H, r H ≤ m H + ind (X.ERec fx H))
    (budget : Ex.E m + Ex.E (fun H => ind (X.ERec fx H)) ≤ T) :
    Ex.E (fun H => max (r H)
      (ind (Runs S I (ctxB X fx (wOf H) H) ∧
        ¬ hb.OutcomeRec (ctxB X fx (wOf H) H) (S.model1 (ctxB X fx (wOf H) H))
          (S.model2 (ctxB X fx (wOf H) H))))) ≤ T
```

`ctxB X fx w H` is the binder block whose pair is the adversary's output at H, and inside the proof `realizes` holds by `⟨rfl, rfl⟩` (`realizes_by_construction`). `realizes_everywhere` shows it holds at every H, so it filters nothing. Realizes is not a hypothesis of either theorem.

Under the owner decision of 2026-11-08, the host averaging will not instantiate `TASB.Expect` with the program-view expectation on the fail indicator. The INP_ reading (section 1.5) is that no program view can determine an arbitrary `wOf H`. The host averaging is therefore the pointwise inclusion `deployed_outer`:

```
∀ wOf H, max (r H) (ind (Runs … (ctxB X fx (wOf H) H) ∧ ¬ OutcomeRec …)) ≤ m H + ind (E_rec H)
```

proved from `RSL.EVB.no_second_charge` and `TASB.fail_sub_rec`. It is followed by `NNH_RecordedCharge.bound` (`lazyMean (recorder … (normalize a) Q) … ≤ accountLoss Q`) and the existing `failureModel ≤ total (Q0+Q1)` chain at `a := normalize a`. Both events live on the same space of oracles H, and the adversary's randomness is part of the adversary program.

#### 1.2.2 Host theorems (compiled; printed kernel statements)

These statements are printed with `set_option pp.all true` and `pp.proofs false` (evidence/integrate-20261111, NNH_L941; source TAS_FinalB.lean, compiled at L939 and in TAS_G0_COMBINED_IMPORT at L945). They are quoted verbatim from TAS_G0_AUDIT.json `kernel_statements_verbatim`. The texts of `fail_sub_rec` and `NNH8_DeployedOuter`, and the "before" text of RPx_Deployed.deployed, are in the same file.

```
@AspisR1.TAS_FinalB.deployed_splitB : ∀ {W Tx : Type}
  (L0 : AspisR1.S2Trust.Library W (Nat → AspisR1.S2W_D189Entry.Record))
  (borrow : @AspisR1.S2Trust.S2TrustedSdkBorrow W (Nat → AspisR1.S2W_D189Entry.Record) L0)
  (copy :
    AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record) →
      Nat → AspisR1.S2Trust.Payload → AspisR1.S2W_TrustedStd.Outcome (Nat → AspisR1.S2W_D189Entry.Record))
  (std : @AspisR1.S2W_TrustedStd.TrustedStd (Nat → AspisR1.S2W_D189Entry.Record) copy)
  (allocation217 : RSL.Bytes → RSL.Env → Bool) (allocation234 : RSL.TX2_234.Args → RSL.Env → Nat → Bool)
  (ch : NMX_R4_Authentication.Choices) (alloc2 : NMV_ConcreteWindows.Allocation) (fx : AspisR1.NOC_Run5bCtx.Fixed)
  (w : AspisR1.NOC_Run5bCtx.World W Tx) (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
  (queries :
    @RSL.TASB.ExecB.QueriesF (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
      (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std) (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx)
  (run :
    @RSL.TASB.Runs (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) NNH_Libraries.L NNH_Libraries.V0 NNH_Libraries.VL
      (AspisR1.NNH_Run6Installed.implementation allocation217 allocation234 ch AspisR1.NNG_Candidate344.allocation
        alloc2)
      (@RSL.TASB.ctxB (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std)
        (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx w H)),
  have c : RSL.TAS.Sig.Ctx (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) :=
    @RSL.TASB.ctxB (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std)
      (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx w H;
  And
    (RSL.TAS.Sig.Bound (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c
      (RSL.TAS.Sig.model1 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c)
      (RSL.TAS.Sig.model2 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c))
    (And
      (@AspisR1.NNH8_Split.rest W Tx L0 copy c (RSL.TAS.Sig.model1 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c)
        (RSL.TAS.Sig.model2 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c))
      (Or
        (@RSL.EVB.HeadlineB.OutcomeRec (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
          (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std) (@AspisR1.NNH8_HeadlineB.headlineB W Tx L0 borrow copy std) c
          (RSL.TAS.Sig.model1 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c)
          (RSL.TAS.Sig.model2 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c))
        (@RSL.TASB.ExecB.ERec (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
          (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std) (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx H)))
```

```
@AspisR1.TAS_FinalB.deployed_charge : ∀ {W Tx : Type}
  (L0 : AspisR1.S2Trust.Library W (Nat → AspisR1.S2W_D189Entry.Record))
  (borrow : @AspisR1.S2Trust.S2TrustedSdkBorrow W (Nat → AspisR1.S2W_D189Entry.Record) L0)
  (copy :
    AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record) →
      Nat → AspisR1.S2Trust.Payload → AspisR1.S2W_TrustedStd.Outcome (Nat → AspisR1.S2W_D189Entry.Record))
  (std : @AspisR1.S2W_TrustedStd.TrustedStd (Nat → AspisR1.S2W_D189Entry.Record) copy)
  (allocation217 : RSL.Bytes → RSL.Env → Bool) (allocation234 : RSL.TX2_234.Args → RSL.Env → Nat → Bool)
  (ch : NMX_R4_Authentication.Choices) (alloc2 : NMV_ConcreteWindows.Allocation) (fx : AspisR1.NOC_Run5bCtx.Fixed)
  (anchor : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
  (queries :
    @RSL.TASB.ExecB.QueriesF (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
      (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std) (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx)
  (wOf : (AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State) → AspisR1.NOC_Run5bCtx.World W Tx),
  And
    (∀ (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State),
      @LE.le.{0} Rat Rat.instLE
        (@Max.max.{0} Rat Rat.instSup (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (RSL.TASB.ind
            (And
              (@RSL.TASB.Runs (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) NNH_Libraries.L NNH_Libraries.V0
                NNH_Libraries.VL
                (AspisR1.NNH_Run6Installed.implementation allocation217 allocation234 ch
                  AspisR1.NNG_Candidate344.allocation alloc2)
                (@RSL.TASB.ctxB (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
                  (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std) (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx (wOf H) H))
              (Not
                (@RSL.EVB.HeadlineB.OutcomeRec (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
                  (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std)
                  (@AspisR1.NNH8_HeadlineB.headlineB W Tx L0 borrow copy std)
                  (@RSL.TASB.ctxB (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
                    (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std) (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx (wOf H)
                    H)
                  (RSL.TAS.Sig.model1 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
                    (@RSL.TASB.ctxB (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
                      (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std) (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx (wOf H)
                      H))
                  (RSL.TAS.Sig.model2 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
                    (@RSL.TASB.ctxB (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
                      (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std) (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx (wOf H)
                      H)))))))
        (RSL.TASB.ind
          (@AspisR1.BinRawByteCollisionTargets.event
            (AspisV8R19.MemoizedProgramLaw.View AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State
              (AspisR1.GExq_AccountExperiment.Outcome Bool))
            (@FS2.Duplex.Params.iv AspisR1.SelectedTranscriptParams.Message AspisWideTower.WideExact
              AspisR1.SelectedTranscriptParams.L AspisR1.SelectedTranscriptParams.params)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (AspisR1.NNH_HostCtx.Fixed.Q0 fx)
                (AspisR1.NNH_HostCtx.Fixed.Q1 fx))
              (@OfNat.ofNat.{0} Nat (nat_lit 2965) (instOfNatNat (nat_lit 2965))))
            (@AspisV8R19.MemoizedProgramLaw.eval AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State
              (AspisV8R19.MemoizedProgramLaw.View AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State
                (AspisR1.GExq_AccountExperiment.Outcome Bool))
              H (AspisR1.NNH8_RecorderFixed.fixedProgram copy fx anchor)))))
    (And
      (@LE.le.{0} Rat Rat.instLE
        (@AspisV8R19.MemoizedProgramLaw.lazyMean AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State
          (AspisV8R19.MemoizedProgramLaw.View AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State
            (AspisR1.GExq_AccountExperiment.Outcome Bool))
          (@Pi.instFintype.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))) =>
              AspisV8R19.DuplexFrames.Byte)
            (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
            (SimplexCategory.instFintypeToTypeOrderHomFinHAddNatLenOfNat
              (SimplexCategory.mk (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))))
            fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))) =>
            SimplexCategory.instFintypeToTypeOrderHomFinHAddNatLenOfNat
              (SimplexCategory.mk (@OfNat.ofNat.{0} Nat (nat_lit 255) (instOfNatNat (nat_lit 255)))))
          (fun (a b : AspisV8R19.DuplexFrames.Bytes) =>
            @instDecidableEqList.{0} AspisV8R19.DuplexFrames.Byte
              (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256)))) a b)
          (AspisR1.NNH8_RecorderFixed.fixedProgram copy fx anchor)
          (@FS.emptyTable AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State)
          fun
            (v :
              AspisV8R19.MemoizedProgramLaw.View AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State
                (AspisV8R19.MemoizedProgramLaw.View AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State
                  (AspisR1.GExq_AccountExperiment.Outcome Bool))) =>
          AspisV8R19.CausalFirstHitUnionBound.indicator
            (@AspisR1.BinRawByteCollisionTargets.event
              (AspisV8R19.MemoizedProgramLaw.View AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State
                (AspisR1.GExq_AccountExperiment.Outcome Bool))
              (@FS2.Duplex.Params.iv AspisR1.SelectedTranscriptParams.Message AspisWideTower.WideExact
                AspisR1.SelectedTranscriptParams.L AspisR1.SelectedTranscriptParams.params)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (AspisR1.NNH_HostCtx.Fixed.Q0 fx)
                  (AspisR1.NNH_HostCtx.Fixed.Q1 fx))
                (@OfNat.ofNat.{0} Nat (nat_lit 2965) (instOfNatNat (nat_lit 2965))))
              v))
        (AspisR1.F3T_Numeric.total
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (AspisR1.NNH_HostCtx.Fixed.Q0 fx)
            (AspisR1.NNH_HostCtx.Fixed.Q1 fx))))
      (∀ (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State),
        have c : RSL.TAS.Sig.Ctx (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) :=
          @RSL.TASB.ctxB (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std)
            (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx (wOf H) H;
        @LE.le.{0} Rat Rat.instLE
          (AspisR1.F3T_RuntimeBound.failureModel
            (@AspisR1.NOC_Run5bHost.runtime W Tx L0 copy c
              (RSL.TAS.Sig.model1 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c)
              (RSL.TAS.Sig.model2 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c)))
          (AspisR1.F3T_Numeric.total
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (AspisR1.NNH_HostCtx.Fixed.Q0 fx)
              (AspisR1.NNH_HostCtx.Fixed.Q1 fx)))))
```

`#print axioms` and the raw ax2 walk (ledger30's walker NNM_ProofDriver 46ee271b…ca3c, NNH_L942 to L944) give exactly `propext`, `Classical.choice` and `Quot.sound` for both theorems. The `deployed_splitB` cone has 146,370 constants and the `deployed_charge` cone has 146,551.

#### 1.2.3 Interface fields that must be closed terms

`top_splitB_physical` takes 22 interface structure arguments besides the libraries, the account counts, the ExecB instance and the context. In the final theorem each must be a delivered closed term of exactly its TAS type, never a hypothesis, `sorry`, variable or trust row (TAS_G0_BRIEF section 0 rule 5). Status at ledger27 (NNK_TOP_COMPOSITION.json) is in the table below and is kept for history. **Status at run 7: every field is a delivered closed term** (TAS_G0_AUDIT.json `field_installations`). The fields are delivered as follows:

- nmn is dropped by ruling (bu)(2).
- nms and g1a take their (bu) forms, `NNT_Field.r241` and `NNT_G1aLaw.field`.
- nmfB is `NNH8_NMF.nmfB`.
- hb is `NNH8_HeadlineB.headlineB`.
- sp is `NNH8_TopHost.split` (`NNH8_Rest.assemble`).
- a0 and r0 come from `NOC_Run5bHost`.
- a1 and a2 are as in section 0.
- a3, a4 and a5 are `NNH8_Acceptance`.
- X, R and rs are in `NNH8_Exec`.

Ledger27 table:

| Field | Content | Status at ledger27 |
|---|---|---|
| nmo, nmp, nmt, nmm, nmx, nms | row roots 136; 137/087; 094/328/345; 217/234; 233; 242/241 | 136, 137, 087, 217, 234 CLOSED; 094, 328, 345, 233, 242, 241 OPEN |
| nmv, nmw | 344/240 and 333/221/330/213 folds | CANDIDATE-FOLD; need the OPEN children |
| nmn | NMN_064 RSL transport | `NMN_064.rslRefines` named, not confirmed delivered |
| TOP:PoolLaws | `LIBB_PoolNoWrite.laws` | CLOSED |
| g1a (TOP:G1a) | Root0-free weak law of actual TX2:064 | CANDIDATE; pending nativeRep, headerRep |
| TOP:G1b | 241/240, 221/213 parametric in library | CANDIDATE; 241 OPEN |
| nmfB (TOP:NMF_B) | Root0 at selected occurrence, or E_rec | OPEN; core `NNC_NMFB.root0_or_rec` merged; cut production open |
| rs (TOP:RecSelect) | Realizes plus TX1 facts give SelectsPair | OPEN at host; `NNC_RecSelect.selects`, `NNH_StateSelect` exist |
| hb (TOP:HeadlineB) | Outcome with bad := E_rec | OPEN; no delivered module |
| sp (TOP:Split) | `concl_iff`, Root0-free `rest` | OPEN |
| r0 (TOP:R0rep) | native Root0 = canonical Root0 | CANDIDATE; pending `selected` |
| TOP:G2 | Root0-free write frame of weak 240 reference | CANDIDATE |
| a0 (TOP:A0) | extraction at native := model | OPEN; digestSource resolved by (bt), host statements uncompiled |
| a1, a2 (TOP:A1, A2) | 345/241 returned arms equal AdapterRw model | OPEN |
| a3, a4, a5 | stage wrappers to D189 first/second; entry to game (d) | CANDIDATE |
| TOP:EntryRep | selected routes | CANDIDATE (stand-in only) |
| X (TOP:RZ-STATE) | literal ExecB at a⊤ | OPEN at host; owner decided the form |
| TOP:AVG | averaged deployed bound | OPEN; compiled at stand-in level only |
| TOP:G0 | final host assembly | OPEN |

### 1.3 Every instantiated binder

Each of these is a substitution of a universally quantified headline binder, proved by `rfl` or by a named lemma. None is a hypothesis, and none is a trust row.

| Binder of RPx_Deployed.deployed | Instantiated as | Authority | Why it is not a restriction |
|---|---|---|---|
| `native1`, `native2` | `stage1_owned`/`stage2_owned (DrvC_Installation.sdk cfg)`, the AdapterRw models | owner decision 2026-11-07; TAS `Sig.model1/2` | The actual code meets the models only through the RSL rows plus A1/A2; `extraction` at native := model then holds by `rfl` (A0) except digestSource, which (bt) supplies. |
| `A`, `allocator`, `state1`, `final1`, `state2`, `final2` | `Bool`, `abortIndicator`, all `true` | ruling (bo); TFM `Alloc` | A returned-Ok actual run had every allocation succeed, since a failed allocation aborts the program. `Alloc.allocator_part` gives the allocator half of accepted1/2 at `true`. |
| type binder `CoreError` (of `indexError : CoreError` and `missing : IDa_Deployed.Uninstalled CoreError`) | `NFN_NEW_GeometryDictionary.CE` (`abbrev CE := NEW_GeometryActual.aspis_core.r0.Error`, NFN_GeometryPart04), so `fx.indexError : CE` | NNH_HostCtx.Fixed; NPI_ statement cross-check (2026-11-10) | The headline's CoreError is the error type of the core library the configuration installs. The installed configuration is the deployed one, whose core error type is the extracted frozen `aspis_core::r0::Error`, so the substitution names the type the deployed code actually uses. The value `fx.indexError` stays universally quantified. Recorded here 2026-11-10; it was missing from earlier versions of this table. |
| `a` (in the pair and in `queries`) | `a⊤ := NNH_StateNormalize.normalize a` | owner decision 2026-11-07 (RZ-STATE) | The allocator state models allocation success, which the deployed attacker does not control. `a` itself stays universally quantified. |
| `e1 data1 state1`, `e2 data2 slot state2` | the outputs of `eval H a⊤.first` and `eval H (a⊤.second …)` | owner condition (4) | Realizes holds by construction at every H. Instantiating `a` to a constant adversary is forbidden. |
| `hashv`, `sha256`, `p1`, `syscall` | `hashAdapter H`, `H`, `⟨fun _ => rfl⟩`, `DGP_HostDigest.syscall` | ruling (bt); DGP_DECISION option (a) | `total_syscall_unique`: the adapter is the only total hashv the RuntimeSyscall row admits. Every consumed run returned, so the model agrees with the runtime on every consumed run. |
| `missing` | `NOC_HostCtx.missingLit c := NNH_Tx2Configuration.select (NNH_CorrectConfiguration.residual (NOC_HostSeed.m0 (envOf c).reservation) (envOf c)) (envOf c)` | ruling (s); INP section 1.6; host-model correction 2026-11-09 | Substitution of a universal binder. The seed is `NNH_HostSeed.m0` with current op1 := `NOC_HostSeed.filled` (heap::filled at 4bb3b3f, under the existing allocator trust row). The old seed left op1 as `.div`, so the old host never accepted a tx1 (NOC_PrepareDiv). `NOC_SeedTransfer` proves by rfl that only current op1 and sdk op10 change. This is a model correction under AGENTS section 4, with one slot and no contract or trust change. `envOf c` is `DGP_HostDigest.envInst c.sha256 fx.pda fx.clock fx.reservation`. The headline left these environment components inside the universal `missing`; here `fx.pda` and `fx.clock` are universal Fixed data (section 1.4), so the substitution quantifies over them rather than fixing them. |
| `extraction`, `accepted1`, `accepted2`, `game` | derived, no longer binders | TAS/TFM/EVB | Derived from the row roots, A0 to A5 and `Runs`. |
| `alloc1` (TX1 window allocation stream) | `AspisR1.NNG_Candidate344.allocation` | AMEND item 7 (finding NNH-G0-F3) | Statement data fixed by ledger30's FIN entry, never a hypothesis. alloc2, allocation217, allocation234 and `ch` stay universally quantified. |
| `admission1`, `admission2`, `RuntimePersistence` | conjuncts of `run.frame` = GameFrame ∧ `NOC_Run5bHost.retained` | NFB_ admission grouping | They are no longer separate binders. They are the same trust rows, stated as facts of the actual run's world (section 1.4). |

### 1.4 Every retained hypothesis

Binder shape of the two kernel statements (section 1.2.2):

- `deployed_splitB` binds `{W Tx} L0 borrow copy std allocation217 allocation234 ch alloc2 fx w H queries run`.
- `deployed_charge` binds `{W Tx} L0 borrow copy std allocation217 allocation234 ch alloc2 fx anchor queries wOf`. It has **no `run`, no `w` and no top-level `H` binder**: H is bound inside each conjunct, the world is the arbitrary function `wOf H`, and `Runs` occurs only inside the failure indicator `ind (Runs … ∧ ¬ OutcomeRec …)`. So `Runs.*`, the admissions and RuntimePersistence are hypotheses of `deployed_splitB` only, and parts of the averaged event in `deployed_charge`.

| Binder / hypothesis | Kind | Notes |
|---|---|---|
| `{W Tx}` | universal types | The Library world type and the bank-transaction index type. Unconstrained. |
| `L0 : S2Trust.Library W (Nat → S2W_D189Entry.Record)` | universally quantified data | The abstract SDK library (the headline's `L`). It is constrained only through `borrow`. |
| `borrow : S2Trust.S2TrustedSdkBorrow L0` | trust (S2TrustedSdkBorrow) | Kernel name `borrow`; it is the headline's `sdk`. All 15 fields are assumed (section 4.3). |
| `copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record)` | universally quantified data | The slice-copy function. It is constrained only by `std`. |
| `std : TrustedStd copy` | trust | W1 qualification retained. |
| `allocation217`, `allocation234`, `ch`, `alloc2` | universally quantified data | Allocation-success streams for the (bn) windows and leaf rows, and the TX2:233 choices. There is no allocator-success trust item (NNK_HANDOFF). `alloc1` is instantiated (section 1.3). |
| `fx : NOC_Run5bCtx.Fixed`, twelve fields | universal | `pda : List Bytes → B32 → Option B32`, `clock : Except ProgramError UInt64`, `reservation`, `indexError : CE`, `root`, `length`, `prior`, `words`, `D`, `a`, `Q0`, `Q1`. `fx.a` is an arbitrary adaptive adversary, never constant. **`fx.pda` and `fx.clock` are new universal data with no headline binder counterpart**: they are the environment's PDA and clock components, previously inside the universal `missing`. Being universal, they restrict nothing. The model and recorder are clock-independent (`NNH8_Exec.clockFree`, in the cones). The physical clock reading is RuntimeClockSlotBinding inside the stage2 window (section 4.2). |
| `w : World W Tx` (deployed_splitB), `wOf` (deployed_charge) | universal | Fields `w1 w2 saved post1 post2 p t u actions`. They may depend on H arbitrarily through `wOf`. |
| `H` (deployed_splitB); `anchor` (deployed_charge) | universal | `anchor` is fixed program data, not a condition on the sampled oracle. |
| `queries : ExecB.QueriesF … fx` (L154) | statement parameter | Classified as the Q of the bound (amendment 2026-10-27 second, item 2). It is not discharged. Exact form: `∀ J K, (ARW_Induced.issued (stage1_owned (NNH_CorrectConfiguration.sdk (seed (envInst J fx.pda fx.clock fx.reservation)) …)) copy NNE_AbortIndicator.allocator CPH_Program.verifier (normalize fx.a) K).length ≤ fx.Q0 + fx.Q1`. The issued-call bound on a⊤ must hold **for every pair** of an environment digest J and a query oracle K (TAS_G0_AUDIT `QueriesF_exact_source`). |
| `run.frame` (deployed_splitB only) | game (a)-(c) plus the two non-trace equalities of (d), conjoined with `NOC_Run5bHost.retained` (admission1, admission2, RuntimePersistence) | Statement of the approved two-transaction game (amendment 2026-10-26 item 2), not an attacker restriction. `NNH8_NonVacuity.frame_recorded` gives its exact unfolding by `Iff.rfl`. |
| `run.trace` (`TraceRep`, deployed_splitB only) | physical trace association, game (d) | Every `.invoke` action of `p.actions t/u` was executed as `entry` at the RSL images, and every non-verifier action is the recorded Pool or runtime action. This hypothesis is where Pool behaviour enters the theorem (section 5). |
| `run.ok1`, `run.ok2`, `run.out1`, `run.out2` (deployed_splitB only) | the attack's success antecedent | Both actual entries returned Ok, with their recorded outputs. |
| admission1, admission2 (inside `run.frame`) | trust (RuntimeEntrypointAdmission) | Conjuncts 1–2 of `NOC_Run5bHost.retained`, not separate binders. |
| RuntimePersistence (inside `run.frame`) | trust | Conjunct 3 of `retained` (`CPR_DataPersistence.TwoTransactionLaw`, ordinary := `CPG_Projection.ordinary p (key 0)`). |
| `count1`, `count2` (3 and 7 accounts) | host facts, not hypotheses | `NNE_EntryArgs.count`. |

*Corrected 2026-11-10 (NPI_ statement cross-check against TAS_G0_AUDIT.json `kernel_statements_verbatim`). The earlier table omitted `{W Tx}`, `L0` and `copy`, called `borrow` `sdk`, listed only `fx.a`, did not separate the two theorems' binder shapes, and did not quote the all-pairs form of `queries`. No statement changed.*

The final theorem must contain no Root0 hypothesis, no hash-injectivity premise, no Realizes premise and no new trust row. The G0 gate (TAS_G0_BRIEF section 7, item 4) requires a written confirmation of each. **Confirmed at run 7** (TAS_G0_AUDIT.json `written_confirmations`):

- There are zero Root0, Realizes and injectivity tokens in the printed statements, and no new trust row.
- `realizes_mk` is the eval-of-map lemma.
- `exhibited_mk` = `rfl`, `eventRec_mk` = `Iff.rfl` and `queries_mk` = `fun _ _ H _ _ h => h H`, each checked by an rfl example. `queries_mk` is the forall-world L154 family, not literally `id`.
- `a` is universal.
- The averaging conditions on nothing.

## 2. Before and after, against the adopted headline

The format follows AGENTS.md section 3. "Before" is `AspisR1.RPx_Deployed.deployed` (kernel statement SHA-256 8ae0107f9dbb7374135912ff9dda3597ad0096023d0deed471b0cd4dcf305523, adopted 2026-10-27). "After" is the split-B host theorem of section 1.2.2.

**Quantifiers.**
- Before: every binder is independent and universal, including the deployed pair `e1 e2 data1 data2 slot state1 state2`, the adversary `a`, `native1 native2`, `allocator`, `hashv sha256 p1 syscall` and `missing`. The pair is not tied to `a`. The only link is `queries`, which bounds `a`'s issued list (EVB section 1.4).
- After: `a` stays universal. The pair is no longer quantified: it is defined as `a⊤`'s execution output at H. `native1/2`, `allocator`, the four states, `hashv/sha256/p1/syscall` and `missing` are instantiated (section 1.3). The per-world binders (`saved post1 post2 p t u actions RuntimePersistence w1 w2 admission1/2`) stay universal and may depend on H arbitrarily (`wOf`).
- Net effect: the new theorem covers fewer free instantiations of model-side binders, and every one of them is justified as a substitution in section 1.3. It covers the adaptive case that the old theorem did not connect to the bound: a pair chosen after querying H is a charged part of `a`. At each H, every pair the old statement covered is also covered, because a constant adversary realizes it with zero queries. The universal statement, however, is a different theorem, not a weakening, because the pair is now bound to the adversary's run. The owner approved this change on 2026-11-07.

**Carriers.** Unchanged: the Aeneas carriers `S2W_ExtractionBoundary.First/Second`, `Slice U8`, `Heap (Nat → Record)`, `Bytes → State`. `A` becomes `Bool`. The RSL carriers (`TX2_240.Args`, `SdkState`, `Env`, `Obs`) are added on the actual-code side and are related to the headline carriers by `EnvRep`, `args1/2`, `state1/2` and `Out1/2`.

**Hypotheses removed or added.**
- Derived instead of assumed: `extraction`, `accepted1`, `accepted2`, `game`.
- Added: `Runs` (frame, trace, ok1, out1, ok2, out2), the actual-run antecedent. `game` was itself a binder before, so this is a re-expression of game (a)-(d) on the actual RSL images plus the actual Ok results, not a new kind of assumption. The earlier `realizes` hypothesis approved on 2026-11-07 is discharged by construction and does not appear.
- Unchanged: `queries`, both admissions, `RuntimePersistence`, `sdk` (kernel name `borrow`), `std`, `copy`.
- Reclassified, not removed: P1 and RuntimeSyscall are no longer Lean premises at the top, because (bt) instantiates them. The rows remain the justification for reading `Runs/TraceRep` at `env c` as the physical run.

**Failure event.**
- Before: conjunct 4 is `FJv_DResult.Outcome … (bad := E_head)`, with E_head the collision event on the fixed-selection program `F3X_Account.program cfg hashv P` with constant selector `fun _ => P2P_NativeSelection.pair … e1 e2 data2 slot`.
- After: conjunct 4 becomes `OutcomeRec ∨ E_rec`, where `OutcomeRec` is Outcome with `bad := E_rec`. E_rec is the event on `ARX_LocalCharge.bounded (ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a⊤) (Q0+Q1)` with selector `ARQ_Observer.select`. Its form (`BinRawByteCollisionTargets.event` at Q0+Q1+2965) is the same, but it is a different event: the adversary's own run rather than a fixed pair.
- The failure event of the probability statement (`failureModel`: accepted run whose extractor returns none, plus query-scan exhaustion) is unchanged. E_rec is the event `failureModel` already charges as `accountLoss`, so no new term enters the bound.
- `F3Y_AccountMass.Claims` for E_head stays in conjunct 5 and remains true, but it is no longer the charge that covers conjunct 4.

**Conclusion.**
- Before: all eleven conjuncts, unconditionally.
- After: C5num and the other ten conjuncts unconditionally, except that conjunct 4 is weakened to `OutcomeRec ∨ E_rec`. Off E_rec, the split form gives exactly the headline shape (`top_split_exact_off_event`, TFM). On E_rec worlds Outcome is lost, and those worlds are already paid for inside total(Q).
- The averaged statement `deployed_charge` is new. The headline had no averaged deployed-failure statement over the actual pair: its numeric conjuncts bound `failureModel runtime`, a function of `a` alone.

**Satisfiability and non-vacuity.** The retained premises are satisfiable: a constant adversary realizes any pair, and `Runs` holds of any actual accepted pair. That the physical predicates `TraceRep` and `GameFrame` are not `False` must be shown by the non-vacuity check of TAS_WIRING item 8, which is a gate item (section 6). No joint real-byte accepted pair exists yet (trust appendix, final paragraphs).

## 3. The numeric claim

### 3.1 The exact bound

The bound is `F3T_Numeric.total`, defined in lean/F3T_Numeric.lean as

```
total(Q) = (Q+34)·B + collisionLoss(Q) + accountLoss(Q) + 2^-126 + 2^-454
B                = PerAttemptEnvelope.B = 15/2^109            (≈ 2^-105.093)
collisionLoss(Q) = 6·(Q+1161)^2 / 2^256
accountLoss(Q)   = 6·(Q+2965)^2 / 2^256
```

Q is the number of digest queries issued by the adversary across both phases, counting duplicates and every call issued before a rejection, taken on `a⊤`. Every term is shown below; nothing else enters.

| Term | Meaning | Source of the constant |
|---|---|---|
| (Q+34)·B | Start charge. Every fresh transcript start, among the adversary's Q queries plus the 34 starts the submitted transcript reads in the prover/sampler prefix before terminal authentication, succeeds with probability at most B. | START-CHARGE-20261021.md; F3T bounds (Q+34 starts) |
| collisionLoss(Q) | Collision mass over at most Q+1161 distinct first reads (verifier envelope 1161, unchanged under frozen3). | frozen3 F3T bounds |
| accountLoss(Q) | E_rec: collision among the recorded reads of the adversary's capped account run, at most Q+1921 first reads plus 1040+4 audit reads = Q+2965. Charged once inside `failureModel` (compiled: `FJp_Residual.numeric`, `le_refl accountLoss`); for the per-attempt event including OutcomeRec the single charge is `no_second_charge` at stand-in level, host theorem pending (finding 4). | `P2P_Charge.binding_or_collision`, `FJp_Mass.bounded` |
| 2^-126 | Extractor abort allowance (accepted, no hit, extractor still returns none). | Lean: `RawRecordedOracleExtractionMassBin.shared_oracle_failure_le_hit_add_abort`, `bankAbortMass_le`; recorded in the contract 2026-10-21 table |
| 2^-454 | Query-scan exhaustion, `QueryScanModelFailure.failureProbability (2^18)`. | Lean: `QueryScanModelFailure.exhaustion_bound`; recorded in the contract 2026-10-21 table |

### 3.2 Per-attempt corollary and its valid range

`F3U_Range.per_attempt`: for Q ≤ maxQueries, total(Q) ≤ (Q+1)·2^-100, where

maxQueries = `F3U_RangeEdges.maxQueries` = 7388980242446479800895501321004157112314840375 ≈ 2^152.372.

`F3U_RangeMaximal.exact_range` proves the converse: total(Q) ≤ (Q+1)·2^-100 holds if and only if Q ≤ maxQueries. Above maxQueries the bound total(Q) still holds, but the (Q+1)·2^-100 form does not. EVB_range.py reproduces maxQueries from exact rationals. Owner decision 2026-11-07: under option B the number and the range are unchanged. Option A would have needed a second accountLoss, with range ≈ 2^151.787, and is not used.

(Q+1)·2^-100 is a corollary of total(Q), not the contract (contract 2026-10-21, "Correction to the lead's adoption addendum"). The binding criteria are (A) and (B) of the contract, stated here as follows.

- **(A), whole experiment with no adversary queries.** `F3T_Numeric.margin_exact`:
  2^-100 − total(0) = 2^-108 − 6·(1161² + 2965²)/2^256 − 2^-126 − 2^-454 > 0.
  Numerically, total(0) = 510/2^109 + 60834876/2^256 + 2^-126 + 2^-454 ≈ 0.99609·2^-100 ≈ 2^-100.0056. The margin is ≈ 0.999996·2^-108. The 2^-100 target is met at Q = 0 with about 2^-108 to spare, and almost all of total(0) is the 34 transcript starts.
- **(B), Q-dependence kept.** For 0 ≤ Q ≤ maxQueries, the failure probability is at most total(Q), which is approximately (Q+34)·2^-105.093 for every Q below about 2^100. The (Q+1)·2^-100 figure is looser than total(Q) by a factor of 2^5.093 (= log2(512/15)) for Q above about 10^4; the factor is about 2^4.9 only near Q ≈ 233 (bound audit, finding 1).

No proof-of-work or grinding credit is used. No probability is divided by adversarial work, and this draft states no work-normalised figure.

### 3.3 Query accounting

- What is counted: `ARW_Induced.issued model1 copy abortIndicator CPH_Program.verifier a⊤ H`, the chronological list of digest calls the induced prover issues across both phases. This includes duplicate queries and every call before a rejection. It is identified with `(eval H P).1.length` by `ARW_Induced.queries` (amendment 2026-10-27, item 1).
- What the verifier adds: the constants 34 (starts), 1161 (distinct first reads), 1921 (first-read budget on the account run) and 2965 (recorded reads for E_rec) are verifier envelopes, charged on top of Q. The issued-call log is at most Q+2322.
- What the attacker's adaptive pair choice costs: under Realizes the pair is the output of `a⊤`, so every query used to choose it is in Q.

### 3.4 Why adaptive selection is covered

Before option B, the charged event in conjunct 4 used a constant selector on a pair quantified independently of `a`. If the pair may be an arbitrary function of H, the probability of that event can be 1 (EVB section 3, a pigeonhole argument, not Lean-checked). Option B removes this gap by construction:

1. The pair is `a⊤`'s output at H.
2. E_rec is evaluated on `a⊤`'s own account run with the output-dependent selector `ARQ_Observer.select`.
3. `F3T_AccountCharge.bound`, the account-mass lemma, holds for any selector applied to the source's own output, and `FJp_Mass` already charges it as accountLoss(Q).
4. `fail_sub_rec` proves that at every H, a successful actual run whose OutcomeRec fails lies in E_rec at the same H.

The inclusion is proved, not assumed (owner condition (2)), and it concerns the actual adversary's execution (owner decision 2026-11-08, item (1)).

### 3.5 Repeated attempts

**Within one experiment.** Repeats are covered. `queries` counts every issued call, including duplicates and rejected prefixes, across both phases. An adversary that tries many candidate transcripts offline before submitting is charged for every query it makes. That is the ROM work metric of the contract.

**Across separately submitted spend attempts.** No theorem in the dependency closure states a multi-attempt bound. The contract amendment of 2026-10-27 (second, item 2) says such campaigns are "accounted for by the per-attempt bound exactly as in the 2026-10-21 contract", and that contract gives the per-experiment form (B). The drafter's reduction is the following. It is not Lean-checked and must be reviewed or proved before publication.

1. For k submitted attempts against the same oracle, attempt i is an instance of the theorem with the adversary a_i that runs everything up to and including attempt i.
2. The world binders are arbitrary, so earlier chain state is covered.
3. a_i must reproduce the verifier's digest calls of earlier attempts as its own queries, at most 2322 per attempt.
4. A union bound then gives Pr[some attempt accepted with failure] ≤ Σ_{i=1..k} total(Q_i). MAT_ (evidence/multi-attempt-20261108, stand-in theorem `RSL.MAT.campaign_charge`/`campaign_bound`, compiled, standard axioms) corrects this sketch: Q_i is the CUMULATIVE issued-call count of the reduction adversary a_i, Q_i ≤ c·(Q_adv,≤i + 2322·(i−1)), with phase factor c = 2 for the current two-phase adversary type (the second phase recomputes the first, `SCE_Experiment.Adversary` carries no private state); c = 1 would need a host argument. Its host obligations H-MA1 (construction of a_i with the submitted inputs as its outputs at every H), H-MA2 (its cost) and H-MA3 (whatever the campaign adversary sees between attempts is a function of H and oracle-free data fixed before H, so a_i can recompute it with charged queries) are not discharged. LEAD READING, 2026-11-08, for the owner: H-MA3 does not restrict what the attacker may observe or adapt to; it is a cost-accounting rule that charges the verifier's digest calls of earlier attempts (2322 each) to the reduction adversary's query count. That is exactly the "work performed through verifier interactions" item the security contract must state explicitly (AGENTS.md section 1); whether the campaign corollary is published in these units, or campaign security stays stated per attempt only, is an owner decision on contract scope, not a proof question.

This sum is not to be replaced by setting a single-experiment bound to 1 (AGENTS.md section 2). If the lead does not accept the reduction, the published claim must say that campaign security is stated per attempt only.

### 3.6 What the number applies to

The number bounds the per-attempt failure of the two-transaction spend experiment: the attack succeeds at H and either the extractor fails or OutcomeRec fails. It applies under the trust inventory of section 4, at the frozen source and configuration of section 1.1. It is not a statement about privacy, Pool settlement, double spending, custody or availability (section 5).

## 4. Trust inventory the theorem relies on

*Reconciled 2026-11-10 by NPI_ (evidence/trust-final-20261110; NPI_TRUST_REACH.json, NPI_TRUST_INVENTORY_PROPOSED.md), adopted by the lead.* Authority: design/TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md as approved and amended, and ledger30 (NNN_LEDGER.json: 25 trust rows, 40 reviewed-transcription entries). The inventory is reconciled one-to-one against the L187 replayed raw ax2 cones of `deployed_splitB` (146,370 constants) and `deployed_charge` (146,551 constants). A Lean constant counts as reached only if it is in both cones. "Enters / used by" names the route by which the row reaches the theorems (4.0). Of the 599 CLOSED rows, 140 have a root in the cones and 7 more enter through restated top fields. For the other 450 the CLOSED certificate is association evidence, not a dependency of the Lean proof (section 7, item 16). Rows that the cones do not reach are kept and marked UNREACHED (4.7). Rows proposed by campaigns but not decided are listed in 4.8 and are not adopted. No row has been removed.

"Confirmed" gives the owner record. "Class authority" means the row was added by the lead under the owner's 2026-11-04 decision ("you can have solana runtime assumptions that seems reasonable"; the lead may add same-class runtime rows, which "must still be recorded as trust rows and reported"). No individual owner confirmation of such a row is recorded in C3-BIN.

### 4.0 Entry routes

| Mode | Meaning |
|---|---|
| BINDER | a universally quantified hypothesis in the printed kernel statement |
| RUN_FRAME | a conjunct of `NOC_Run5bHost.retained` inside `S_host.GameFrame`. It is the hypothesis `run.frame` in deployed_splitB, and it sits inside the averaged event `Runs` in deployed_charge, where it is not a hypothesis |
| INSTANTIATED | the Lean structure is built by a term at the top. The row stays as the physical reading of what the term models |
| WINDOW | a window law of the (bn) stage1/stage2 fission, consumed by `NMV_ConcreteWindows.root240/root344` |
| LEDGER | a CLOSED ledger row whose root, or whose restated top field, is in the cones uses the row |
| META | the frozen function that makes the call is on the deployed path whose model is in the cones, but the CLOSED certificate root that uses the row is not in the cones. The row is needed to read the model as the physical run, not for the Lean proof |
| TOOL | tool trust (extraction, Kani, compiler), reached whenever its output is in the cones |

### 4.1 Oracle and cryptographic model

| Row | Exact statement | Enters / used by | Removal condition | Confirmed |
|---|---|---|---|---|
| Random-oracle model for SHA-256 (frozen3 security/oracle model, L194) | SHA-256 as invoked through the runtime hash syscall is a uniformly random function H : Bytes → State. Every probability is over H. | Statement: `failureModel`, `lazyMean`, E_rec and deployed_charge. | None. A standard-model argument would be a different theorem. | Contract 2026-10-26 §1 |
| P1 ideal-oracle realization `S2W_ExtractionBoundary.P1.realization` | ∀ bytes, sha256 bytes = H bytes, at the supplied world. | INSTANTIATED: sha256 := H, p1 := rfl (ruling (bt)). `P1.mk` and `P1.realization` are in the cones. The row justifies reading the physical hash replies in `Runs` as values of H. | None; inherent to the ROM reading. | Appendix 2026-10-27 |
| RuntimeSyscall.returningValue | hashv parts = ok d → decodeState d = sha256 (flatten parts). No totality. | INSTANTIATED by the theorem `DGP_HostDigest.syscall` at `hashAdapter H`. `RuntimeSyscall`, `.mk`, `.returningValue` and `S2Z.Oracle.RuntimeSyscall` are in the cones. The row is the physical reading of every returned digest in `Runs`. | A proved realization of the pinned runtime's `sol_sha256` syscall (Agave syscall handler at the deployed validator version) returning the SHA-256 of exactly the passed slices. | Contract 2026-10-26 §3 |
| RuntimeSha256Value | The SolanaDigest/hashv reply value realises H. Exact request slices and an unchanged reply are separate bridge obligations; op43/op44 are digest/error. | META: the ledger lists retained-value uses TX1:327 and TX2:210, but their NGC_ roots are not in the cones. The row is reached because every accepted run reads hashv replies as H (`AdapterRw.SolanaDigest`, `DGP_HostDigest.hashvInst`, `RSL.Event.digest` are in the cones). | **Proposed (new):** for the value-equals-H part, none (it is the ROM reading, as for P1). For the realization part, a proof that the pinned `sol_sha256` implementation returns the SHA-256 of the exact passed slices; that proof would reduce this row to P1. | Ledger: ACCEPTED retained trust (contract 2026-10-21) |

### 4.2 Solana runtime behaviour (owner decision 2026-11-04)

| Row | Exact statement | Enters / used by | Removal condition | Confirmed |
|---|---|---|---|---|
| RuntimeEntrypointAdmission (verifier; `AdapterRw.RuntimeEntrypointAdmission` seven fields: valid, freshGuards, noExternalBorrows, liveAccount, counterZero, sharedCellsOnlyEqualKeys, duplicateKeysShareCell; plus wrapper fields `S2W_D189Consolidation.RuntimeEntrypointAdmission.entry/related`) | At each of the two verifier entries (3 and 7 accounts): initial heap validity, fresh guards, zero counters and external borrows, live accounts, key/cell alias consistency. | RUN_FRAME: conjuncts 1–2 of `NOC_Run5bHost.retained` (`RuntimeEntrypointAdmission L c.i.entry c.world.w1 3 ∧ … c.j.entry c.world.w2 7`). The whole structure is assumed. Only `.valid`, `.entry` and `.related` are projected inside the cones. | **Proposed (new):** a proved realization of the pinned input serialization of the deployed BPF loader (Agave, version recorded by NDZ) together with `solana_program::entrypoint::deserialize` at solana-program 2.3.0, establishing the seven fields at both entries. A field-by-field discharge is possible because the cones project only valid/entry/related, but the binder still assumes all fields. Narrowing the hypothesis would be a statement change and needs the AGENTS §3 before/after audit. | Contract 2026-10-26 §3 |
| RuntimePersistence (`CPR_DataPersistence.TwoTransactionLaw`) | ∀ t u, next t u → ∀ key, ordinary t key → loaded u key = visible (if success t then tentative t key else before t key). Data bytes only; zero lamports means absent. | RUN_FRAME: conjunct 3 of `retained`, at `ordinary := CPG_Projection.ordinary p (Hist_Nonvacuity.key 0)`. That excludes signing accounts and accounts owned by the all-zero System program, a restriction of the approved domain. The historical `S2X.CheckpointVersionBinding` is constructed from this row (4.5). The ledger trust row lists no consumers, which is stale. | **Proposed (new):** a proved realization of the deployed validator's account commit and load between consecutive transactions on one bank lineage (accounts-db store after a successful parent, unchanged on failure) for ordinary accounts. No such proof exists for Agave; the honest current status is "none available". | Owner amendment 2026-10-26 §3 |
| Allocator (data-only `S2W_D189Wrappers.Allocator`) | allocate/cleanup with no success proposition. | INSTANTIATED: allocator := `NNE_AbortIndicator.allocator`, states := true (ruling (bo)). The physical reading "a failed allocation aborts" is NOX_ line D.5 (section 4.8). | Not applicable as a free binder. The physical reading's condition is that of D.5. | Contract 2026-10-26 §3 |
| RuntimeClockSlotBinding | clockGet ctx = ok v → v = bankSlot ctx, within one instruction context. Nothing about success, monotonicity or epochs. | WINDOW: `Clock::get()` at r1_pool_adapter_owned.rs:479 through `NMV_WindowClock.exact_clock`. `RSL.Env.clock` and `RSL.Event.clock` are in the cones. `fx.clock` is a universal Fixed field and `NNH8_Exec.clockFree` gives clock-independence of the model and recorder. | A proved realization of the pinned Clock sysvar (`sol_get_clock_sysvar` at the deployed validator version). Already recorded. | ADDED-LEAD-20261105, class authority. Individual confirmation not recorded. |
| RuntimeReturnDataClear (ruling (am)) | An empty set_return_data within one instruction leaves no return data observable by get_return_data until a later set. | WINDOW: `program::set_return_data(&[])` at owned.rs:467, a window law of `NMV_ConcreteWindows.root240` (in the cones); `RSL.Event.returnData` is in the cones. The ledger record still says `used: false`, which is stale against ruling (bn) and FIN_240. | A proved realization of the pinned runtime's return-data register (`sol_set_return_data` / `sol_get_return_data`). Already recorded. | ADDED-LEAD 2026-11-06, class authority. Individual confirmation not recorded. |
| RuntimeReturnData (ruling (ab), (ab')) | For 1 ≤ \|b\| ≤ 1024: set_return_data(b) by P, then an immediate get_return_data in the same instruction context with no intervening CPI, returns Some((P, b)). | META: `emit_result` is called by `stage2_owned` (TX2:241, reached through `NNT_Field.r241`). Its CLOSED consumer TX2:219 (NFY_Part058/059 roots) is not in the cones. The Pool-side readback association is OPEN and is outside the theorem. | **Proposed (new):** a proved realization of the pinned runtime's return-data register, the same deliverable as RuntimeReturnDataClear. | ADDED-LEAD 2026-11-04; **OWNER ACCEPTED 2026-11-04** |
| RuntimeMemcmp (ruling (ac)) | For the same two valid readable 688-byte ranges: normal return into the supplied i32 slot, zero iff all bytes are equal, no other effect. | META: `scan_proof_buffer` (its 688-byte compare) is called by `validate_asq8` (TX2:242; `NMX_R6_Validation.root` is in the cones). Its CLOSED consumer TX2:226 (NFY_Part060 roots) is not in the cones. | The trust-reduction packet on the pinned validator's `sol_memcmp_` (recorded, not commissioned). | ADDED-LEAD 2026-11-04; **OWNER ACCEPTED 2026-11-04** |

### 4.3 Library and SDK

| Row | Exact statement | Enters / used by | Removal condition | Confirmed |
|---|---|---|---|---|
| S2TrustedSdkBorrow (15 fields, solana-account-info 2.3.0) | The fifteen fields of `AspisR1.S2Trust.S2TrustedSdkBorrow L0`: data-borrow and RefCell guard semantics. No caller result. | BINDER `borrow` in both kernel statements. All 15 fields are assumed; only `account_data_cell` and `cell_payload` are projected inside the cones. Ledger consumers: 330/333/213/221/240, reached through the installed fields. | **Proposed (new):** a Lean proof of the fifteen fields against an extraction of the pinned solana-account-info 2.3.0 `AccountInfo::try_borrow_data / try_borrow_mut_data` and the pinned `core::cell::RefCell / Ref / RefMut` (guard acquire, move, deref, drop), once an extractor handles guard drop. The pinned Aeneas currently fails on guard drop (ruling (be)(2)), so today there is no tool route. | Appendix 2026-10-27 |
| TrustedStd (`S2W_TrustedStd.TrustedStd.slice_copy_from_slice`; W1) | Pinned `slice::copy_from_slice` on valid borrowed references: equal lengths copy into the destination payload only; unequal lengths panic. The abstract law quantifies all states, so each use needs justified validity (W1). | BINDER `std` in both kernel statements; the `copy` binder is constrained only by it. Ledger consumers: the 17 composed rows. | **Proposed (new):** a Lean equality between `copy` on the valid domain and the pinned Aeneas Std model of `core::slice::copy_from_slice`, together with the W1 validity fact at each use in the cones. This is a proof task: the row then reduces to the P7 library base. | Appendix 2026-10-27 |
| TrustedStd (Port1: `option_ok_or`, `result_unwrap32`) | Pure Option/Result interpretations. | Not reached as a hypothesis: `AspisR1.Port1_Library.TrustedStd` is not in the cones. The cones use the concrete `Port1_LibrarySource.okOr/unwrap32` models through `Port1_Library.std`. | Kept. The std reading of those concrete models is PROPOSED-HM-C (section 4.8). | Appendix 2026-10-27 |

### 4.4 Translation, tool and realization trust

| Row | Exact statement | Enters / used by | Removal condition | Confirmed |
|---|---|---|---|---|
| AeneasExtraction (D188, trace fidelity; narrowed by D188-P3 and (bc)) | Trace fidelity: the pinned Charon/Aeneas translation of each associated frozen body preserves the accepted Result and the chronological attempted digest-call sequence, with rejected prefixes both rejecting. Narrowing (D188-P3): bodies that fail the dropped-restoration scan or native differential get no credit and are bridged natively. Narrowing (bc): "faithful except explicit returns or `?` in post-loop code merged into a loop exit; every emitted body relied on must be shown free of that pattern, or the affected exits certified natively." | INSTANTIATED at the top (`a0 := NOC_Run5bHost.a0`; both `AeneasExtraction` structures and their `.mk` are in the cones). TOOL for every emitted body in the cones. The (bm) emitted-body reclassifications for TX1:136/137/087/094/328/345 and TX2:234/233/242 have their roots in the cones; 241/333/221/330/213 enter through installed fields. | None for the tool. For release, every reached emission must be receipted or proved equal to a fresh emission (note (bk), gate row 7). | Owner 2026-10-27 (trace fidelity) |
| P6 / Kani association (K-1 narrowing, (br)) | Pinned Kani/CBMC as evidence for checked associations between the frozen body and its reference. Credit only without copy builtins, or with the KMX element-wise copy stubs (sha256 bcdf749b…a9a67) and a matched failing negative control. Timeouts earn nothing. | TOOL: the native halves of every hybrid row on the deployed path. | None for the tool. | Appendix 2026-10-27; amendment fourth |
| NativeContractSemanticTransport (amendment fifth) | Kani's and Aeneas's interpretations of the enumerated frozen bodies and references denote the same Rust semantics, plus the recorded association of the entries with native1/native2, the digest wrapper with op43, and the external digest with hashv. | TOOL + LEDGER: `consumes_trust` of the 17 composed rows; 380 direct CLOSED rows, of which 84 have a root in the cones. NLT-TX2:065 (`NLT_CompleteRoot.root` in the cones) is reached. NMN-TX2:064 (`NMN_064.root`) is not in the cones because TX2:064 left the top by (bu). | **Proposed (new):** none for the tool (a clarification of P6/D188). Per use, it is removed when the Kani+Aeneas pair is replaced by a single-tool route: an emitted body of the actual frozen function proved equal to the reference, with no Kani step. | Owner 2026-10-28 (amendment fifth) |
| P7 compiler/LLVM/platform and pinned Lean/Mathlib/Aeneas base | The selected compiler/toolchain/ABI and the pinned Lean/Mathlib/Aeneas base, for the exact recorded source, features and toolchain. | TOOL: the whole closure. NOX_ lines D.1–D.4 (section 4.8) are its concrete SBF instances. | None for the tool. | Appendix 2026-10-27 |
| AllocatorABICompilerSourceToELF | Retained realization boundary: binding to the concrete final artifact. | LEDGER `consumes_trust` of the 17 composed rows; the physical reading of (bo). | Already recorded as a "RETAINED ROOT REALIZATION OBLIGATION", discharged only by L188. NOX_ has met the reproduction half (both ELFs byte-identical from 4bb3b3f). The remaining content is split into the PROPOSED NOX_ lines D.1–D.7 (section 4.8). | Ledger (obligation, not an approved trust row) |
| Standard logical axioms | `propext`, `Classical.choice`, `Quot.sound` only. | KERNEL: walked = collected = these three for all four roots on the replayed objects. | None. On the L187 replayed closure (879,350 constants, 19,862 modules) there are 105 nonstandard axiom declarations, the same set as 2026-10-27 (84 formatter native_decide, 21 Lean/Aeneas infrastructure); none is reachable from any of the four roots (NPI_L004). Strict import-wide standard-only still fails (F-AXIOM). | Appendix 2026-10-27 |
| **CheckedVsWrapping (R22, OPEN)** | The gate's emitted bodies are Aeneas translations compiled with overflow checks ON (historical extraction configuration `CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true`, `RUSTFLAGS=-C overflow-checks=yes`), so every integer operation is checked and an overflow is an error result. The deployed R1 ELFs were built by cargo-build-sbf with the plain release profile (receipts `evidence/finish-pair2-20261027/FJd_SBF_default.json`, `FJd_SBF_devnet.json`; the frozen Cargo.toml enables overflow-checks only for aspis-r1-cert-check and aspis-r1-cert-build), so the deployed code WRAPS. The theorem is about the checked semantics; its transfer to the deployed binary needs, on every reached path, either totality (no checked operation fails, so both semantics agree: `R22TotalCheckedComposition`) or the direction wrapping-acceptance implies checked-acceptance with the same result. Status 2026-11-10 (NPH_, evidence/r22-final-20261110/NPH_R22_FINAL_COUNTS.md; the 2021 census figures are superseded): of 197 executed checked or mixed definitions in the cone (28 further definitions are proof-only references, NOT_EXECUTED by the backward referrer screen), 72 TOTAL, 52 DIRECT (a single bounded increment or bounds-checked read as the only checked operation), 68 with the precondition proved from the callers (all six field-kernel families, both canonical.Q.raw copies TOTAL, the dots/accumulate/residue bodies via the S7JoinRowsTrace.Progress cadence invariant and new window invariants, the cursor, decoder and sampler bodies), 5 OPEN: binary_step (an unguarded len(nodes) − s.at where a wrapped difference below 32 would take the accepting Stop branch while the checked model aborts; closes with the traversal invariant s.at ≤ len(nodes), no reached state violating it is known), weights.field (finish-dot index bound at the deployed finish), values_owned_reference (len ≤ 1856 through expandValues), prepare (the installed op15 constant), r24_canonical_mul (no frozen counterpart; source-refinement obligation). 55 of the 393 CLOSED rows these definitions serve still depend on an OPEN definition. No reachable input on which the wrapping binary accepts and the checked model rejects is known. Textual-screen reliances (site checklist, call-chain and dictionary readings, the backward referrer screens, the checked-operation lists behind DIRECT) are listed in section 4 of that file and must each become a Lean statement or an owner-named review item. | Every CLOSED row on the emitted-body route, through the source-to-ELF association (L188). | Discharged by the R22 totality audit closing on the final closure (every reached cone TOTAL or its precondition established by the caller join), or stated as a retained trust row by the owner. Recorded here 2026-11-09 after Stream C's provenance campaign found the configuration difference (checked gate versus wrapping fresh emissions). | Not owner-decided. |

### 4.5 Constructed, not assumed

| Row | Status |
|---|---|
| Historical `S2X.CheckpointVersionBinding.*` and `S2W_AuthenticatedInputs.CheckpointVersionBinding.history` | Reached as constructed terms (`CPR_DataBinding.binding`, `CPG_History.on_cuts`: "None of its three ledger fields is an input"), built from RuntimePersistence, the game and source proofs. They are never a hypothesis. This matches the appendix's "no additional trust". |

### 4.6 Reviewed transcriptions (class ReviewedTranscription; P6/D188 option-A reclassification under amendment fifth, never removal)

The class is owner-approved (2026-10-28, option A). Every item was added by the lead under rulings (ah), (ay), (bc)(4), (bg) or (bn). C3-BIN records "reported to the owner" for (bn) and for the Pool items. No individual owner confirmation of any item is recorded.

| Item | Rows | Reached | Removal condition |
|---|---|---|---|
| ReviewedTranscription-TX1:344 ((bn), 2026-11-07) | TX1:344 | YES: `NMV_ConcreteWindows.root344` through `NVR_TasRoots.field344` | A native certificate on the actual frozen `stage1` (recorded) |
| ReviewedTranscription-TX2:240 ((bn), 2026-11-07) | TX2:240 | YES: `NMV_ConcreteWindows.root240` through `NVR_TasRoots.field240` | A native certificate on the actual frozen `stage2` (recorded) |
| ReviewedTranscription-TX2:217 ((ah), 2026-11-07) | TX2:217 | YES: `NMX_R3_DecoderFold.root` | A native certificate on the actual frozen `decode_lane_from_pool_release`, paired with the same emitted reference and with no reviewed-transcription reliance (recorded) |
| ReviewedTranscription-prepared_claim ((ah), 2026-11-06) | TX1:193, 179, 186 | YES: `NGU_PreparedClaim.packet` (TX1:193) | An emitted body of `prepared_claim` proved equal to the transcription (recorded) |
| ReviewedTranscription-polynomial ((ah)) | TX2:119 | YES: `NHE_Polynomial.cohort`, `NHE_WidePort.adopted` | **Proposed (new):** an emitted body of `verifier.rs::polynomial` from the pinned extractor (or an approved successor) proved equal to the NHE_ reverse-fold transcription |
| ReviewedTranscription-queries_from_pairs ((ah), 2026-11-06) | TX1:168, 179, 186 | YES, only through the shared root `AspisR1.RPx_Deployed.deployed`. The item's own roots (`NGP_TRANSCRIPT.actual_queries`, `NHK_*`) are not in the cones. Kept as reached (conservative). | An emitted body of `queries_from_pairs` proved equal to the transcription (recorded) |
| NKL-RT-batch_tree ((bc)(4)) | TX1:081–083, TX2:053–055 | YES for the TX2 rows (`NLN_TX2_055.root` is in the cones); the TX1 root `NLN_TX1_083.root` is not | See the per-item table below |

The 36 unnamed verifier items, each with its own removal condition. Reachability of these entries was first tested on certificate roots: 28 entries had neither the item's certificate root nor any root of its rows in either cone. NPI_L005 (finding F2, section 7 item 17; evidence/trust-final-20261110/NPI_F2.json) then settled each of the 28. An entry is REACHED when a model in the cones is defined from its certificate or reference model (the installed `AdapterRw.Ops` slots and RSL library children), or when its certificate is stated about a model in the cones. Otherwise it is NOT REACHED. Entries are kept either way. Each item keeps its own removal condition.

| Item | Rows | Frozen function | Kind | Reached (evidence) | Removal condition (proposed) |
|---|---|---|---|---|---|
| NJY-RT149 | TX2:149 | decode_pool_identity_v1 | reviewed hand Rust reference (NJQ_reference.patch) with Lean model theorem NJQ_*.source | REACHED (F2, definition): NJQ_Identity.model is in the cones (used by NJQ_Master, installed through op48 := NKF_MasterBox.reference := NKF_BoxModel.outer (NJQ_Canonical.master)); NJQ_Identity.source states reference = model | An emitted body of decode_pool_identity_v1 from the pinned extractor (or an approved successor) proved equal to the NJQ_ hand reference (NJQ_reference.patch and its Lean NJQ_*.reference), the (ah) class default; the reviewed Rust reference then leaves the trust base. |
| NJY-RT152 | TX2:152 | decode_pool_v1_pair_forest_checkpoint_v1 | reviewed hand Rust reference (NJQ_reference.patch) with Lean model theorem NJQ_*.source | REACHED (F2, definition): installed op49 := NKF_CheckpointBox.reference, built on NJQ_Canonical.checkpoint := mapOuter … (NJQ_Checkpoint.model) (NND_DecoderSlots.install, in the host adapter chain); NJQ_Checkpoint.source states reference = model | An emitted body of decode_pool_v1_pair_forest_checkpoint_v1 from the pinned extractor (or an approved successor) proved equal to the NJQ_ hand reference (NJQ_reference.patch and its Lean NJQ_*.reference), the (ah) class default; the reviewed Rust reference then leaves the trust base. |
| NJY-RT153 | TX2:153 | decode_pool_v1_pair_forest_master_v1 | reviewed hand Rust reference (NJQ_reference.patch) with Lean model theorem NJQ_*.source | REACHED (F2, definition): installed op48 := NKF_MasterBox.reference := NKF_BoxModel.outer (NJQ_Canonical.master …) = NJQ_Master.model; NJQ_Master.source states reference = model | An emitted body of decode_pool_v1_pair_forest_master_v1 from the pinned extractor (or an approved successor) proved equal to the NJQ_ hand reference (NJQ_reference.patch and its Lean NJQ_*.reference), the (ah) class default; the reviewed Rust reference then leaves the trust base. |
| NJY-RT201 | TX2:201 | decode_verifier_registry_entry_v1 | reviewed hand Rust reference (NJQ_reference.patch) with Lean model theorem NJQ_*.source | REACHED (F2, definition): installed op32 := NJQ_Canonical.entry := mapOuter entryResult (NJQ_Entry.model …); NJQ_Entry.source states reference = model | An emitted body of decode_verifier_registry_entry_v1 from the pinned extractor (or an approved successor) proved equal to the NJQ_ hand reference (NJQ_reference.patch and its Lean NJQ_*.reference), the (ah) class default; the reviewed Rust reference then leaves the trust base. |
| NJY-RT203 | TX2:203 | decode_verifier_registry_v1 | reviewed hand Rust reference (NJQ_reference.patch) with Lean model theorem NJQ_*.source | REACHED (F2, definition): installed op31 := NJQ_Canonical.registry := mapOuter registryResult (NJQ_Registry.model …); NJQ_Registry.source states reference = model | An emitted body of decode_verifier_registry_v1 from the pinned extractor (or an approved successor) proved equal to the NJQ_ hand reference (NJQ_reference.patch and its Lean NJQ_*.reference), the (ah) class default; the reviewed Rust reference then leaves the trust base. |
| NJZ-RT189 | TX1:189 | echeck | reviewed native patch NJZ_native.patch | REACHED (F2, proved equal): NJZ_CodecSemantics.source : parsedStep b k = LPl.Echeck.chunk b.val k, where NFU_Retarget.LPl.Echeck.chunk is the echeck model in the cones | An emitted body of echeck proved equal to the NJZ_ transcription, or a native certificate on the actual frozen function without the reviewed patch. |
| NJZ-RT201 | TX1:201 | pool_v1_tree_parent | reviewed native patch NJZ_native.patch | NOT REACHED (F2): NJZ_TreeParent: 0 of 14 declarations in the cones; statement mentions no cone constant | An emitted body of pool_v1_tree_parent proved equal to the NJZ_ transcription, or a native certificate on the actual frozen function without the reviewed patch. |
| NJZ-RT202 | TX1:202 | IncrementalMerkleTreeV1::default | reviewed native patch NJZ_native.patch | NOT REACHED (F2): NJZ_PoolRoot: 0 of 11 declarations in the cones; statement mentions only Nat/Fin instances | An emitted body of IncrementalMerkleTreeV1::default proved equal to the NJZ_ transcription, or a native certificate on the actual frozen function without the reviewed patch. |
| NJZ-RT203 | TX1:203 | IncrementalMerkleTreeV1::empty | reviewed native patch NJZ_native.patch | NOT REACHED (F2): as NJZ-RT202 | An emitted body of IncrementalMerkleTreeV1::empty proved equal to the NJZ_ transcription, or a native certificate on the actual frozen function without the reviewed patch. |
| NJZ-RT204 | TX1:204 | pool_v1_empty_roots | reviewed native patch NJZ_native.patch | NOT REACHED (F2): as NJZ-RT202 | An emitted body of pool_v1_empty_roots proved equal to the NJZ_ transcription, or a native certificate on the actual frozen function without the reviewed patch. |
| NKJ-RT036 | TX1:036 | qm31_accumulate_product_channels | frozen segment/reference/native loop assembly (ruling (ah)) | NOT REACHED (F2): NKJ_* modules: 0 declarations in the cones; statements mention only exact-tower carriers; no cone model of qm31_accumulate_product_channels | An emitted body of qm31_accumulate_product_channels from the pinned extractor (or an approved successor) proved equal to the transcription, or one native certificate on the actual frozen function covering the whole body without cuts or fission. |
| NKJ-RT044 | TX1:044 | qm31_sum_products_small | frozen segment/reference/native loop assembly (ruling (ah)) | NOT REACHED (F2): as NKJ-RT036 (qm31_sum_products_small) | An emitted body of qm31_sum_products_small from the pinned extractor (or an approved successor) proved equal to the transcription, or one native certificate on the actual frozen function covering the whole body without cuts or fission. |
| NKJ-RT040 | TX1:040 | qm31_sum_products2 | frozen segment/reference/native loop assembly (ruling (ah)) | NOT REACHED (F2): statement mentions only PoseidonPreparedKaratsubaValue.QMExact/decodeQM carriers (qm31_sum_products2) | An emitted body of qm31_sum_products2 from the pinned extractor (or an approved successor) proved equal to the transcription, or one native certificate on the actual frozen function covering the whole body without cuts or fission. |
| NKJ-RT041 | TX1:041 | qm31_sum_products3 | frozen segment/reference/native loop assembly (ruling (ah)) | NOT REACHED (F2): as NKJ-RT040 (qm31_sum_products3) | An emitted body of qm31_sum_products3 from the pinned extractor (or an approved successor) proved equal to the transcription, or one native certificate on the actual frozen function covering the whole body without cuts or fission. |
| NKJ-RT043 | TX1:043 | qm31_sum_products4 | frozen segment/reference/native loop assembly (ruling (ah)) | NOT REACHED (F2): as NKJ-RT040 (qm31_sum_products4) | An emitted body of qm31_sum_products4 from the pinned extractor (or an approved successor) proved equal to the transcription, or one native certificate on the actual frozen function covering the whole body without cuts or fission. |
| NKM-RTNGB002 | TX1:NGB002 | circle_fallback_point | frozen native callee/iteration cuts (ruling (ah)/(ay)) | REACHED (F2, proved equal): NKM_Adopted.fallback is stated about AspisR1CircleFallback.transcript.circle_fallback_point, the model in the cones | An emitted body of circle_fallback_point from the pinned extractor (or an approved successor) proved equal to the transcription, or one native certificate on the actual frozen function covering the whole body without cuts or fission. |
| NKM-RTNGB004 | TX1:NGB004 | secure_ood_circle_point_from_parameter | frozen native callee/iteration cuts (ruling (ah)/(ay)) | REACHED (F2, proved equal): NKM_Adopted.ood is stated about circle.secure_ood_circle_point_from_parameter, in the cones | An emitted body of secure_ood_circle_point_from_parameter from the pinned extractor (or an approved successor) proved equal to the transcription, or one native certificate on the actual frozen function covering the whole body without cuts or fission. |
| NKM-RTNGB006 | TX1:NGB006 | secure_circle_point_from_parameter | frozen native callee/iteration cuts (ruling (ah)/(ay)) | REACHED (F2, proved equal): NKM_CircleModel.circle_source is stated about AspisR72Sampler.circle.secure_circle_point_from_parameter, in the cones | An emitted body of secure_circle_point_from_parameter from the pinned extractor (or an approved successor) proved equal to the transcription, or one native certificate on the actual frozen function covering the whole body without cuts or fission. |
| NKI-RT234 | TX1:234 | append_level_packed_selector_tensor | frozen native callee/iteration cuts (ruling (ah)/(ay)) | YES: AspisR1.NKI_AppendRoot.source | An emitted body of append_level_packed_selector_tensor from the pinned extractor (or an approved successor) proved equal to the transcription, or one native certificate on the actual frozen function covering the whole body without cuts or fission. |
| NKI-RT260 | TX1:260 | semantic_initial_and_absorption | frozen native callee/iteration cuts (ruling (ah)/(ay)) | YES: AspisR1.NKI_InitialRoot.source | An emitted body of semantic_initial_and_absorption from the pinned extractor (or an approved successor) proved equal to the transcription, or one native certificate on the actual frozen function covering the whole body without cuts or fission. |
| NKI-RT233 | TX1:233 | add_value_lanes | frozen native callee/iteration cuts (ruling (ah)/(ay)) | REACHED (F2, proved equal): NKI_ValueRoot.source is stated about FIq_Native…add_value_lanes and NKI_ValueAssociation.reference, both in the cones | An emitted body of add_value_lanes from the pinned extractor (or an approved successor) proved equal to the transcription, or one native certificate on the actual frozen function covering the whole body without cuts or fission. |
| NKL-RT084 | TX1:084 | canonical_scan | frozen native callee/iteration cuts (ruling (ah)/(ay)) | REACHED (F2, definition): the installed library child LIBC_CanonicalScan.good/value/child (in the cones) is defined from NKL_Checks.checks, the check sequence of the NKL native certificate | An emitted body of canonical_scan from the pinned extractor (or an approved successor) proved equal to the transcription, or one native certificate on the actual frozen function covering the whole body without cuts or fission. |
| NKU-RT124 | TX2:124 | resume | frozen native parent/child cuts | YES: NKU_ParentFold.source | An emitted body of resume from the pinned extractor (or an approved successor) proved equal to the transcription, or one native certificate on the actual frozen function covering the whole body without cuts or fission. |
| NKY-RT235 | TX1:235 | append_levels_packed_selector_tensor | frozen native parent/child cuts | REACHED (F2, proved equal): NKY_LevelsComplete.source equates the literal transcription with NKI_LevelsFrame.run, in the cones | An emitted body of append_levels_packed_selector_tensor from the pinned extractor (or an approved successor) proved equal to the transcription, or one native certificate on the actual frozen function covering the whole body without cuts or fission. |
| NKY-RT216 | TX2:216 | decode_checkpoint_box | frozen native parent/child cuts | REACHED (F2, proved equal): NKY_BoxSource.checkpoint / NKY_BoxTotal.checkpoint are stated about NKF_CheckpointBox.reference = installed op49 | An emitted body of decode_checkpoint_box from the pinned extractor (or an approved successor) proved equal to the transcription, or one native certificate on the actual frozen function covering the whole body without cuts or fission. |
| NKY-RT218 | TX2:218 | decode_master_box | frozen native parent/child cuts | REACHED (F2, proved equal): NKY_BoxSource.master / NKY_BoxTotal.master are stated about NKF_MasterBox.reference = installed op48 | An emitted body of decode_master_box from the pinned extractor (or an approved successor) proved equal to the transcription, or one native certificate on the actual frozen function covering the whole body without cuts or fission. |
| NKR-RT-225 | TX1:225 | qm31_sum_products_up_to4 | frozen native parent/child cuts | NOT REACHED (F2): NKR_SumCarrier: 0 declarations in the cones; statement mentions only carriers; no cone model of qm31_sum_products_up_to4 | An emitted body of qm31_sum_products_up_to4 from the pinned extractor (or an approved successor) proved equal to the transcription, or one native certificate on the actual frozen function covering the whole body without cuts or fission. |
| NKR-RT-232 | TX1:232 | add_schedule_lanes | frozen native parent/child cuts | YES: AspisR1.NKR_ScheduleRoot.source | An emitted body of add_schedule_lanes from the pinned extractor (or an approved successor) proved equal to the transcription, or one native certificate on the actual frozen function covering the whole body without cuts or fission. |
| NKR-RT-251 | TX1:251 | public_digest_packed_selector_tensor | frozen native parent/child cuts | NOT REACHED (F2): NKR_DigestComposed: 0 declarations in the cones. Its references are explicitly not equated with the cone's old FIq_Native public_digest_lanes ('association … remains a separate obligation', NKR_DigestComplete); the statement only adds that the old model returns a canonical value | An emitted body of public_digest_packed_selector_tensor from the pinned extractor (or an approved successor) proved equal to the transcription, or one native certificate on the actual frozen function covering the whole body without cuts or fission. |
| NKR-RT-250 | TX1:250 | public_digest_packed | frozen native parent/child cuts | NOT REACHED (F2): as NKR-RT-251 | An emitted body of public_digest_packed from the pinned extractor (or an approved successor) proved equal to the transcription, or one native certificate on the actual frozen function covering the whole body without cuts or fission. |
| NKR-RT-220 | TX1:220 | finish_selector_tensor_basis | frozen native parent/child cuts | NOT REACHED (F2): NKR_SumFinishComposed: 0 declarations in the cones; statement mentions only carriers; no cone model of finish_selector_tensor_basis | An emitted body of finish_selector_tensor_basis from the pinned extractor (or an approved successor) proved equal to the transcription, or one native certificate on the actual frozen function covering the whole body without cuts or fission. |
| NKR-RT-218 | TX1:218 | evaluate_with_selectors | frozen native parent/child cuts | REACHED (F2, proved equal): NKR_SumCopyRoot.source is stated about FIq_Native…evaluate_with_selectors, in the cones | An emitted body of evaluate_with_selectors from the pinned extractor (or an approved successor) proved equal to the transcription, or one native certificate on the actual frozen function covering the whole body without cuts or fission. |
| NKL-RT-batch_tree | TX1:081, TX1:082, TX1:083, TX2:053, TX2:054, TX2:055 | batch_merkle, batch_merkle_values, batch_tree | frozen native callee/iteration cuts (ruling (ah)/(ay)) | YES: TX2:053, TX2:054, TX2:055 | An emitted body of candidate.rs::batch_tree/batch_merkle/batch_merkle_values from the pinned extractor (or an approved successor) that passes the (bc) post-loop-exit check, proved equal to the explicit-Result f_ref transcription on the same arrays and histories; or a native certificate on the actual frozen functions without the transcription. |
| NLH-RT-261 | TX1:261 | semantic_packed | frozen native parent/child cuts with abort association | YES: AspisR1.NLH_SemanticFold.source | An emitted body of semantic_packed from the pinned extractor (or an approved successor) proved equal to the transcription, or one native certificate on the actual frozen function covering the whole body without cuts or fission. |
| NLH-RT-237 | TX1:237 | composition_parts | frozen native parent/child cuts with abort association | YES: AspisR1.NLH_CompRoot.source | An emitted body of composition_parts from the pinned extractor (or an approved successor) proved equal to the transcription, or one native certificate on the actual frozen function covering the whole body without cuts or fission. |
| NLH-RT-263 | TX1:263 | terminal_parts | frozen native parent/child cuts with abort association | YES: AspisR1.NLH_PartsRoot.source | An emitted body of terminal_parts from the pinned extractor (or an approved successor) proved equal to the transcription, or one native certificate on the actual frozen function covering the whole body without cuts or fission. |
| NLH-RT-256 | TX1:256 | r0::Public<'a>::terminal_qm31 | frozen native parent/child cuts with abort association | YES: AspisR1.NLH_WrapperRoot.source | An emitted body of r0::Public<'a>::terminal_qm31 from the pinned extractor (or an approved successor) proved equal to the transcription, or one native certificate on the actual frozen function covering the whole body without cuts or fission. |

Of the 37 inventory entries (36 items plus batch_tree), 24 are reached and 13 are not. Nine are reached through a certificate root in the cones and 15 through F2. The 13 not reached are NJZ-RT201/202/203/204, NKJ-RT036/040/041/043/044 and NKR-RT-220/225/250/251.

### 4.7 Kept and marked UNREACHED

| Row | Evidence | Would enter if |
|---|---|---|
| RuntimeCpiAccountView (Stream C (c-a), ADDED-LEAD-20261110) | No Pool CPI constant in either cone; Pool CPI sites only. | (aj)(a) puts Pool execution in the game |
| RuntimeEntrypointAdmission-Pool ((ap), ADDED-LEAD-20261107) | Pool entrypoint only. | the same |
| ReviewedTranscription-POOL324, 345, 296, 320, 223, 332 (ADDED-LEAD-20261110) | Pool rows only; 0 verifier CLOSED rows. | the same |
| RuntimeCpiReadonlyEntry7 | ADDED-PENDING-LEAD, never admitted, unused. | an admission decision |
| FixturePdaRuntime (lead, standing delegation, 2026-10-28 late) | 0 JHs_/JHw_/JHt_ constants in either cone. op38 is quantified in the theorem. | the non-vacuity witness of gate row 5 is built on the fixture |
| NMN-TX2:064 native-contract-semantic-transport reclassification | `NMN_064.root` is not in the cones (ruling (bu)(3)(a): TX2:064's root left the top). | the top reinstates the 064 field |

All UNREACHED rows stay in the inventory as they are. The claim's first sentence must mention the Pool rows if (aj)(a) chooses the conditional boundary.

All UNREACHED rows stay in the inventory as they are. The claim's first sentence must mention the Pool rows if (aj)(a) chooses the conditional boundary.

### 4.7a Rows accepted on 2026-11-10 under the owner's delegation to Stream C ("you decide just get it working"), reported by Stream C and entered by the lead; additions only

| Row | Assumes | Used | Removal condition |
|---|---|---|---|
| **SdkTypeModels (PROPOSED-HM-A, ACCEPTED 2026-11-10)** | The gate-side Lean types and functions standing for the Solana SDK items Pubkey (as Array U8 32), Hash, PubkeyError and ProgramError, with their clone/eq/as_ref/create_program_address/new_from_array/to_bytes methods, are faithful models of the pinned crates (solana-pubkey 2.4.0, solana-hash 2.3.0, solana-program-error, frozen Cargo.lock at 4bb3b3f). | 6 entries in 4 gate modules (AspisR1WithdrawalCaller.Types, NHJ_SnapshotReference.Types, NMT_first.Funs, NMT_stage1_owned.Funs); 42 CLOSED rows; reached by the deployed_splitB cone. | The SDK items are given as extracted-and-compared definitions of the pinned crate versions (a P1 extraction plus Lean equality), or each consumer is shown to use only the byte-array content so that the model is the identity. |
| **CoreSliceIteratorModel (PROPOSED-HM-B, ACCEPTED 2026-11-10)** | The gate definitions of core::slice::chunks_exact_mut and ChunksExactMut::next (P6ToBytes.StdModel.MutableIterator and the same-named externals) and the core array/slice iterator instances (Iter, IterMut, IntoIter, into_iter, next) behave as the pinned Rust core library (rustc nightly-2026-06-01 sysroot, tool pins PCQ_*_PINS.json) on the reached arguments. Same class as TrustedStd, outside its slice_copy_from_slice scope. | 25 entries, 13 names in 10 gate modules (WideToBytes, NEI_PushRaw, NID_ResumeEmission, NJA_CountBody/Multiproof, RPu_FIq_Native, RPz7_WAdm_Fissioned); 145 CLOSED rows; reached by the cone. | The iterator models are replaced by Aeneas library definitions proved equal to a Lean specification of the std semantics, or the consumers are re-extracted with index-based loops that do not call the iterator. |
| **CrossCrateConstantEncoding (PROPOSED-HM-O, ACCEPTED 2026-11-10)** | An Aeneas external axiom standing for a cross-crate constant denotes the transparent value of that constant in the pinned crate, as Aeneas encodes cross-crate constants; used for the constants not yet shown equal by their own fresh definition (STATE_ONLY_HIDING mask, Native07 selected_claim, Native13 COPY_PATTERNS). | The CONDITIONAL_ON_BINDING provenance records (6 in the cone) and the P3d/P2h constant-binding upgrades. | Removed constant by constant as each one's own fresh definition is proved equal to the gate constant (M31/QM31 ZERO/ONE already done, PCQF_E007). |
| **ShrAmt (verified bridge, not trust; PROPOSED-HM-L, recorded 2026-11-10)** | The shift-amount bridge (amount read as Rust `as u32` into the U32 library shift) equals Rust's wrapping shift for every I32 and Usize amount in the overflow-checks-off configuration (NPE_ShrAmt.lean, standard axioms; evidence/shramt-20261110). Residuals: no SBF-target build check; shared Lean usize width. Never reuse for checked shifts with amounts wider than 32 bits. | fibre_point (NFN_ExtractedGeometry) and the transport row family; 35 provenance records upgraded. | Discharged; the residuals close with an SBF-target run of NPE_shift_test.rs. |

| **CoreOptionResultCombinators (PROPOSED-HM-C, entered 2026-11-10 under the owner's trust-boundary decision)** | The Lean definitions of Option::ok_or, Result::map, Result::map_err, the Option Try::branch and FromResidual::from_residual instances, the Option equality instance and the alloc TryReserveError type are the Rust core/alloc semantics of those items at the extraction toolchain (charon-driver's rustc nightly-2026-06-01 for the MIR; RUSTUP_TOOLCHAIN nightly-2026-09-17 recorded alongside, per the per-definition inventory), for the instantiations Aspis code uses. Members and consumers: evidence/prov-p3g-20261110/PCVG_TRUST_ROWS.md. No differential check. | 21 entries in 15 gate modules; 205 CLOSED rows; reached by the cone. | Replace by the Aeneas library definitions with one generic equality lemma per combinator (one exists: PRVEq_S1NativeCompactModelV1_okor_f1); the row stays until consumers use the library definition. |
| **CoreArraySliceOps (PROPOSED-HM-D, entered 2026-11-10)** | The Lean definitions of Array::map, slice/array PartialEq, slice windows, slice first and the RangeFull slice-index operations are the Rust core semantics at the same toolchain, for the instantiations used; core::array::from_fn is EXCLUDED (the array_from_fn_copy bridge, HM-M, stays a proof item). 14 of the unresolved core/alloc/std externals are members. No differential check. | 9 entries in 7 gate modules; 128 CLOSED rows. | Aeneas library definitions plus a generic lemma per operation, or re-extraction without the operation. |
| **CoreNumOpsIterModels (PROPOSED-HM-F, entered 2026-11-10)** | The Lean definitions of u16 count_ones and trailing_zeros with their auxiliary lemmas, Range clone, the Rev and RangeInclusive folds (revFold, rangeFold, range_clone_usize) and the default Iterator::all/any methods are the Rust core semantics at the same toolchain. One unresolved external is a member. Differential check: gate count_ones and trailing_zeros against compiled Rust on all 65,536 u16 inputs, hashes equal (PCVG_DIFFCHECK_HMF.json; run with rustc 1.93.0, not the pinned sysroot, so a plausibility check). | Reached by the cone (members in PCVG_TRUST_ROWS.md). | Prove each against the Lean integer library, or re-extract through Aeneas library definitions. |
| **AeneasDiscriminantHelpers (PROPOSED-HM-G, entered 2026-11-10, narrowed)** | The ImportUnionNamedDiscriminant registration attribute and the transport.Variant discriminant reading are accepted as Aeneas tooling post-processing. NARROWED by the lead: read_discriminant on Aspis's own enums is Aspis-side and stays a proof item (prove each equals the match-based discriminant). No differential check. | Reached by the cone (members in PCVG_TRUST_ROWS.md). | Emit the Aeneas-native form, or prove the registration's reading equals the match-based discriminant. |

Addendum to SdkTypeModels (HM-A): member added 2026-11-10: solana_sdk_ids.bpf_loader_upgradeable.id (solana-sdk-ids 2.2.1); the 16 unresolved solana externals fold into this row. Of the 99 unresolved externals: core/alloc/std 15 (14 to HM-D, 1 to HM-F), solana 16 (HM-A), aspis frozen 68 entries (41 names) which remain OPEN Aspis-side obligations (PCVG_EXTERNALS_BY_CRATE.json; name-prefix classification).

| **ReviewedTranscription-PublicPreparation.public_bytes (ADDED-LEAD-20261110)** | The Lean transcription NPL_PublicBytesRef.public_bytes of the frozen accessor at crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:2017-2077 (callees 2005-2010 and 1327-1361; file sha256 4e209947…787e, lines sha256 46feab61…a312, rev 4bb3b3f) preserves its behaviour; the gate definition AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes (emitted from the mirror crate aspis_r1_public_preparation, not from the frozen file) is proved equal to it as functions (NPL_PublicBytes.gate_eq) and total with fixed output length 1455/1427 bytes (NPL_PublicBytes.gate_total_length), standard axioms (evidence/public-bytes-20261110). Carrier conventions (M31 as U32, Digest as 8-element array) are part of the reviewed claim. | The transcript/challenge equality PRVEq_PP_l4 (Stream C P3l), which was conditional on this accessor; through it every row reaching the public preparation. | An Aeneas emission of public_bytes proved equal to the gate definition. |

| **ReviewedTranscription-FieldDerives (ADDED-LEAD-20261110)** | The derived Clone and PartialEq impls on M31 (crates/aspis-core/src/field.rs:22), CM31 (field.rs:254), QM31 (field.rs:431) and WideExact (crates/aspis-core/src/field/wide_exact.rs:27) at 4bb3b3f have the semantics of field-wise clone and field-wise equality in declaration order; the Lean transcription PCVQ_DeriveRef (evidence/prov-p3q-20261110/PRVEq_DeriveRef_q1.lean, scope PCVQ_L025, standard axioms) is reviewed line by line against the quoted derives, and the deployed clone slot (fun x => ok x) and the equality slots are proved equal to it. Derived impls cannot be named as Charon roots, so no emission exists to compare. | The tx2 resume chain (deployed_tx2_common_q / _authenticated_q) and every installed slot that clones or compares these field types. | A Charon root extracting the derived Clone::clone and PartialEq::eq impls for these four types at the matching configuration, with a proved equality to the transcription. |

**Owner decision 2026-11-10 (trust boundary).** The trust boundary is the frozen Aspis source: Aspis's own code is proved; everything outside it (the Rust core, alloc and std libraries, the Solana SDK crates, the compiler and linker, the runtime syscalls) is trusted by a named row with a precise statement and is not proof work. Accordingly the Option/Result combinators, array/slice operations (except the array_from_fn_copy bridge), num/ops/iter models and Aeneas discriminant helpers become trust rows of the same form as the three above (texts to be entered when Stream C delivers them), and the at most 99 unresolved externals are classified by crate and join those rows where they are library items. Proof budget stays on Aspis-side items: the array_from_fn_copy bridge, the parametric records and compact.OFF_* constants, the frozen-extraction equalities, the gate-only definitions and the checked-versus-wrapping obligation. This supersedes the next sentence's "to be proved" list for the library classes.

Decided NOT to be trust rows (to be proved): Option/Result combinators, array/slice ops, num/ops/iter models, discriminant helpers, array_from_fn_copy (23 blocked dependants stay OPEN until the per-instantiation bridge is proved), the parametric records and compact.OFF_* constants. The at most 99 unresolved externals remain open obligations. The 8 gate-only definitions with no frozen counterpart are source-refinement obligations, not assumptions. Cut modules without a recovered source take the frozen route (fresh = gate equalities against 4bb3b3f emissions, no bridge re-route) except S1Claim* and S1ValuesOwnedModelV1 (ReconstructedSource, never counted frozen-equal). Recorded by Stream C in ~/aspis-streamc-infra/HANDOVER-STREAMC.md.

### 4.8 PROPOSED, not adopted

**These rows are not part of the trust inventory.** They are campaign proposals awaiting classification by the lead or the owner (trust row, proof task or discharged). None of these is a trust row today. Each needs a lead or owner classification: trust row, proof task, or discharged.

| Id | Proposed statement | Reach evidence | Proposed removal condition | Source |
|---|---|---|---|---|
| PROPOSED-HM-A SDK type models | Gate-side Lean types and functions for Pubkey, Hash, PubkeyError, ProgramError (clone/eq/as_ref/create_program_address/new_from_array/to_bytes) are faithful to solana-pubkey 2.4.0, solana-hash 2.3.0 and solana-program-error 2.2.2 on the behaviour the consumers use. | Gate modules NMT_first.Funs and NMT_stage1_owned.Funs are in the splitB cone (3 same-name constants, 5 module hits). | An extraction of the pinned crate items with a Lean equality, or a proof that each consumer uses only the `Array U8 32` content. | PCXD_TRUST_PROPOSALS.md (pre-notified by zk-11) |
| PROPOSED-HM-B core slice iterator model | The gate models of chunks_exact_mut / ChunksExactMut::next and the array/slice Iter, IterMut, IntoIter, into_iter, next_back instances are the pinned core iterators. | 20 same-name cone constants; 24 module hits. | Replace by Aeneas library definitions proved against a Lean std spec, or re-extract with index loops. | the same (pre-notified) |
| PROPOSED-HM-O cross-crate constant encoding (one line) | A fresh external axiom of type Result X for a cross-crate constant is linked to a transparent gate value. The link is an encoding assumption, proved only for M31/QM31 ZERO/ONE. | Affects the equality credits of the provenance campaign (gate row 7), not a cone premise. | A proof of the link for each remaining constant (STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS, Native07 selected_claim, Native13 COPY_PATTERNS, parametric transports). | the same |
| PROPOSED-HM-L ShrAmt bridge (verified, overflow-checks OFF only) | `Std.Usize.wrapping_shr/shl x y := Aeneas wrapping_shr x (toU32 y)` with I32/Usize instances equals Rust's wrapping shift for all amounts. | Underlies 35 EQUALITY_PROVED and 2 EQUALITY_DOMAIN provenance definitions (PCXD_SHRAMT_UPGRADED.json). | **Discharged** by NPE_ (bridge_shr/shl_i32/usize, standard axioms). Recommend recording it as a verified bridge, not trust, with the binding restriction "never reuse for checked shifts with amounts wider than 32 bits". The residual "Lean Usize width = target width" is the library-wide Usize model under P7. | NPE_SHRAMT_CHECK.md (commit b7a8ad98847) |
| CheckedVsWrapping (R22), owner decision only | The row is recorded in 4.4 as an OPEN obligation; what is undecided is whether the owner retains it as trust if the totality audit does not close. | Every checked-configuration emitted body in the cones (NOX_R22_CONFIG.json: 24 checked modules, 2 wrapping, 71 undetermined). | Every reached cone TOTAL or its caller precondition proved on the final closure; otherwise the owner records it as a retained trust row named in the claim's first sentence. | section 4.4; NOX_ line 8 |
| D.1 P7-SBF-Compiler | platform-tools v1.52 rustc 1.89.0-dev (d95c95b6…6002) preserves the semantics of the frozen source (wrapping release profile, panic=abort, bounds and division checks). | Whole deployed ELF. | None for the tool. | NOX_REALIZATION.md line 1 |
| D.2 P7-LLVM-LLD | anza LLVM/clang/LLD 20.1.7 (78496716) for sbpf-solana-solana preserves the LLVM IR semantics. | the same | None for the tool. | line 2 |
| D.3 P7-cargo-build-sbf | cargo-build-sbf 3.1.13 and cargo 1.89.0 select the recorded flags and strip the ELF (reproduced bit-exactly, not proved). | the same | None for the tool. | line 3 |
| D.4 P7-Registry-Crates | The registry sources are those the Cargo.lock checksums name (solana-program 2.3.0, entrypoint, BumpAllocator, syscall stubs). | the same | An archived registry snapshot with per-file hashes, or a vendored build. | line 4 |
| D.5 AllocatorABI (BumpAllocator, in-program) | The runtime maps a heap region at HEAP_START_ADDRESS of at least the requested size; any out-of-region access or allocation failure terminates the instruction with an error and no committed state. | The (bo) abortIndicator reading; NOC_HostSeed.filled. | A proved realization of the pinned runtime's heap mapping and abort semantics. | line 5 |
| D.6 SBF-Loader/VM | The deployed loader loads the ELF with the recorded headers, applies .rel.dyn, resolves the ten imports to their documented syscalls, and executes SBF semantics, including the 4 KiB frame limit. | The whole deployed execution; the syscall rows of 4.2 cover individual syscalls. | A proved realization of the pinned loader and VM. | line 6 |
| D.7 Stack frames | The 34 "Stack offset exceeded" symbols are absent from the linked ELF (name-level check, not a frame-size proof). | the same | A frame-size proof for the surviving functions. | line 7 |

Also proposed by PCXD_ and not decided: HM-C (Option/Result combinators), HM-D (array/slice ops), HM-F (num ops/iter folds), HM-G (discriminant helpers). PCXD recommends treating these as proof tasks. Further proposals are HM-E (alloc models; owned by this audit's allocator item), HM-I (frozen-crate item models and gate-side adaptations, 122 entries), HM-K (other, 32 entries), HM-M (array_from_fn_copy) and HM-N (parametric records including `AdapterRw.Ops`). `AdapterRw.Ops` has 54 constants in the cones, so HM-N is reached. PCXD_EXTERNALS.json lists 99 externals as unresolved (an upper bound) that no existing row covers.

### 4.9 Stale ledger consumer records (noted; no ledger row changed)

1. The `RuntimePersistence` trust row lists no consumers. It is consumed at the top through `run.frame`.
2. The `RuntimeReturnDataClear` record says `used: false` and "no CLOSED full stage2 row". TX2:240 is CLOSED (FIN_240) through the (bn) windows that use this law.
3. The `RuntimeSha256Value` and `RuntimeReturnData`/`RuntimeMemcmp` consumers (TX1:327/TX2:210, TX2:219, TX2:226) are certificates whose roots are not in the cones. Their trust is reached as META, not through those roots.
4. TX1:059 and TX2:040 have no recorded root (NKT-F3, still OPEN).

### 4.10 Not trust, but stated parts of the theorem

These are listed so they are not mistaken for discharged assumptions:

- the query budget L154 (a statement parameter; its exact all-pairs form is in 1.4);
- the two-transaction game (a)-(d) in `Runs.frame/trace` (classified G, a statement of the experiment);
- the actual-run antecedent `Runs.ok1/ok2/out1/out2`;
- the allocation streams `alloc1/alloc2`.

The seven historical checkpoint interfaces (`S2X.CheckpointVersionBinding.*` and `…history`) are reached only as constructed terms. They are never hypotheses (4.5; appendix, "no additional trust").

## 5. What is explicitly NOT claimed

- **Privacy.** Stream B's contract, including the side-channel scope of D159, is separate. Nothing here bears on it.
- **Pool execution, and owner decision (aj)(a).** The theorem does not prove anything about the Pool program. It retains, in `Runs.trace`, the hypothesis that every non-verifier action in the recorded lineage is the recorded Pool or runtime action. Settlement (Pool B/D) is therefore not covered. Decision (aj)(a), Pool inside the admitted game or the headline reported conditional on the external Pool consumer association, is PENDING. Ledger27: Pool production_closed 0, inventory only, K086 unresolved. If the owner chooses the conditional reporting boundary, this claim must say "conditional on the Pool consumer association" in its first sentence.
- **Extraction provenance (note (bk)), a release blocker.** NMH_/NML_: of 336 emitted Lean blobs without a hash-linked pin receipt, 18 were reproduced, 317 were not, and 2 differ semantically outside the canonical domain. By conservative name matching, 566 of 587 CLOSED rows reach at least one unreproduced blob (ledger27; per new row: TX1:137 133, TX1:087 174, TX2:217 0, TX2:234 20). This is not a counterexample and reopens no row, but no release claim may be made until fresh receipted re-extraction plus per-definition equality theorems cover every reached emission. A definition without an equality proof keeps its rows conditional.
- **Cold release replay (L187) and the ELF link (L188).**
  - L187 was closed for the RPz8 cohort. The split-B top's closure has not had a coherent cold replay. Ledger27 states "Not a cold release replay".
  - L188 (final trust/axiom audit and source-to-ELF association) is not closed. The native bridges concern the frozen Rust source as compiled for Kani, not the deployed ELF bytes.
  - The ELF pins are inherited, not rebuilt: default f8c0ec72…43d4, devnet 63ad3e9c…4299.
- **K086 liveness.** `core::cell::panic_already_mutably_borrowed::do_panic::runtime` (core/cell.rs:898) is an unsupported runtime-formatted panic: 1/1024 failed, 12 unreachable. Production reachability or exclusion is unproved, and (aj)(a) is pending. This is a liveness/abort question. Soundness is a statement about accepted runs, so an abort cannot produce an accepted false spend, but no credit for reachability or exclusion is taken.
- **Double-spend prevention, custody and availability.** These are separate properties with their own contracts. Soundness of acceptance does not imply them.
- **Also not claimed:**
  - joint real-byte non-vacuity beyond the gate check of section 6;
  - mainnet deployment;
  - the client/prover recipe (features and constant-time decoding, LOG D272);
  - the D188-P2 deployed attribution at the five retired-preparation interfaces, unless the final audit shows those interfaces are covered by native-bridge rows (section 7);
  - any work-normalised or attack-cost figure.

## 6. Gate evidence required before "established" may be used

Each item needs a committed artifact. Rows 1 to 4 are the G0 gate of TAS_G0_BRIEF section 7. Rows 5 to 15 are release obligations from the contract, AGENTS.md section 8 and the rulings.

1. **Rows.** A ledger with 599 CLOSED, 0 QUALIFIED, 0 OPEN, produced by an all-slices composition gate (raw ax2 walk standard-only over every required root, NFX scan exit 0 with zero dangling references, duplicate owners or import defects, predecessor statements unchanged). Its open_findings must be reconciled with its row statuses (section 7, item 8).
   *Status 2026-11-09: MET.* Ledger30 (evidence/ledger30-20261111, NNN_) has 599/0/0, a raw ax2 walk, NFX scan L009 exit 0 and NKB-F1 resolved. The run-7 closure rescan (NNH_L948) also exits 0: 20,019 modules, 0 dangling references, 0 duplicate owners and 0 import defects.
2. **Top fields.** Every field in section 1.2.3 filled by a delivered closed term of exactly its TAS type, checked by `example : <delivered> = <field type> := rfl`. TAS_G0_MISSING.json must be empty. A `deployed_splitB_conditional` theorem never counts.
   *Status 2026-11-09: MET.* evidence/integrate-20261111/TAS_G0_MISSING.json lists no fields. The a1/a2/sp.rest rfl checks are in TAS_FinalB (NNH_L939); the other fields are accepted at their exact types by `NNT_TopL.top_splitB_physical` (NNH_L938).
3. **Host theorems compiled.** `AspisR1.TAS_FinalB.deployed_splitB` and `AspisR1.TAS_FinalB.deployed_charge` compiled in the combined import, with:
   - raw ax2 walk and `#print axioms` showing only `propext`, `Classical.choice` and `Quot.sound`;
   - no `sorryAx` and no custom axiom;
   - the exact target, exit status, wall time, peak RSS, swap, source revision and source/object hashes recorded per scope (AGENTS.md workflow rule 6).

   *Status 2026-11-09: MET.* TAS_G0_COMBINED_IMPORT is NNH_L945: exit 0, 48.8 s, 6,881,368 KiB, swap 0, at the 8G cap. The raw ax2 walks are NNH_L942 to L944 and are standard-only. Per-scope records are in NNH_Run7_COMPILE.tsv and TAS_G0_EXPORT.json.
4. **Statement audit.** The printed kernel statements of both theorems are quoted verbatim in this document in place of section 1.2.2. A before/after diff against RPx_Deployed.deployed's kernel text confirms in writing:
   - no Root0 hypothesis, no hash-injectivity premise, no Realizes premise and no new trust row;
   - `realizes_mk`, `exhibited_mk`, `queries_mk` and `eventRec_mk` are `Iff.rfl`, `rfl` or `id` (or the eval-of-map lemma for a⊤);
   - `a` is universal and not constant;
   - the averaging conditions on nothing.

   *Status 2026-11-09: MET.* The statements are quoted in section 1.2.2 (NNH_L941). The diff and confirmations are in sections 1.3 and 1.4 and in TAS_G0_AUDIT.json `before_after` and `written_confirmations`.
5. **Non-vacuity.** For an arbitrary actual run, a `World` and the `Runs` facts are constructed from a recorded trace, showing `TraceRep` and `GameFrame` are the physical facts and not `False` (TAS_WIRING item 8). Status 2026-11-10: PARTIAL. NNH8_NonVacuity (definitional World), NPN_RecordedFrame and NPN_RecordedHost (evidence/nonvacuity-20261110) prove from the recorded 10 November transfer pair that GameFrame, Game, TraceRep, Out1/Out2, both entrypoint admissions, RuntimePersistence, the query bound and the retained trust facts are the recorded physical facts; runs_of_residual states the remainder exactly: trace, ok1, out1, ok2. Those four need the reference verifier's acceptance of the recorded bytes, which the host at the deployed ids (finding 19) makes possible; the route is a computable host instance plus either an executable check (timing probe pending) or per-call symbolic evaluation with the oracle fixed as the run's query table (estimate 200-600 scopes). The release instance for this row is NPO_FinalB.deployed_splitB at NPO_Run5bHost.S_host (deployed ids), independently replayed by leanchecker. Executable evidence 2026-11-10 (evidence/nonvacuity-20261110, NPP_L012): a computable copy of the deployed-id host dictionary, every copied definition proved equal to the original (NPP_SdkNovEq.eq), ran the model's stage1_owned in the Lean interpreter on the recorded 10 November transfer's first transaction (accounts, instruction data, Clock slot 520606640) and returned Ok with 1,768 bytes equal to the recorded checkpoint post-image, in 22.7 s, making 18,176 hash calls over 568 distinct queries whose digests were all reproduced offline. This is an executable check, not a proof, and discharges none of trace/ok1/out1/ok2; it shows the model accepts a real run and fixes the intermediate values the per-call proofs will target. Remaining estimate for the row: 160-500 scopes (computable copies of I.entry, tx1Value and tx2Value; about ten existential-selection sites need a reviewer decision).
   *Status 2026-11-09: PARTIAL.* `NNH8_NonVacuity` (NNH_L941) proves several things: `worldOf` builds a World from recorded data; GameFrame, Game, TraceRep and Out1 are, by `Iff.rfl`, the recorded CPG/CPH/trace and carrier facts rather than `False`; Out1 is inhabited; and Exhibited, EnvRep and Realizes hold at every world. No `Runs` inhabitant has yet been constructed from an actual recorded accepted deployed pair (section 7, item 12).
6. **Averaging obligations.** DGP O1 (recorder at `hashAdapter H` equals recorder at a fixed returning hashv) and O2 (recorder independent of the env's sha256 at missingLit) are proved, or a failure is reported. The same-recorder `rfl` (INP section 1.7) is checked.
7. **Extraction provenance.** Every emission reached by a credited root is reproduced from an archived input with the pinned tools, or re-extracted with per-definition equality theorems (note (bk)). The provenance status line reads zero unreproduced blobs reached.
8. **Coherent cold replay (L187)** of the final dependency closure, in the pinned workspace, under capped scopes. Not cached imports. Status 2026-11-10: MET (evidence/replay-l187-20261109/L187_FINAL_REPORT.md). All 14,101 project modules of the TAS_FinalB closure rebuilt from committed sources in a fresh workspace on Lean v4.32.0 under capped scopes (10,815 byte-identical to the cached objects, 3,245 declaration-identical, 38 differing only in compiler-generated auxiliary lemmas, 3 proof-only coherence repairs with statements frozen: NND_Tx2Values, GammaCandidateTotalityV14, NNH_Stage1PrepareDomain; 0 failed). On the replayed objects alone: combined import exit 0, #print axioms standard for deployed_splitB, deployed_charge, fail_sub_rec and NNH8_DeployedOuter, raw ax2 walk standard-only with reachable sets byte-identical to run 7's, NFX scan zero defects over 19,864 modules, kernel statements byte-identical to run 7's. Finding recorded: the cached run-7 closure contained 56 modules compiled against stale import versions (three needed proof repairs; none of the differing constants lies in the final theorems' cones); the theorems are credited on the replayed closure.
9. **Final audit (L188).** Trust and axiom audit of the final closure, together with the source-to-ELF association for the release verifier ELFs (f8c0ec72… and 63ad3e9c…, or newly reproduced pins), including the AllocatorABICompilerSourceToELF realization. Status 2026-11-09 (NOX_, evidence/l188-20261109): the source-to-ELF half is MET for reproduction: both release ELFs rebuilt byte-identically from 4bb3b3f with platform-tools v1.52 (default f8c0ec72…, devnet 63ad3e9c… = the deployed CSnhzGdH… program, no upgrade authority); the 27 October FJd builds had set CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL=3 and did not reproduce the pins. Deployed profile: opt-level 3, overflow checks OFF (wrapping), panic=abort, no LTO; NOX_R22_CONFIG.json lists the 24 checked-configuration gate modules R22 must cover. Realization chain and retained tool-trust lines in NOX_REALIZATION.md. Status 2026-11-10 (NPI_, evidence/trust-final-20261110), audit half. Axiom audit on the replayed closure: **MET**. The four roots print and walk exactly propext, Classical.choice and Quot.sound on the replayed objects. The closure (879,350 constants, 19,862 modules) holds 105 nonstandard axiom declarations, the 2026-10-27 set unchanged, and none is reachable from either theorem (NPI_L004). Trust audit: done, not MET. Reachability is recorded row by row (NPI_TRUST_REACH.json; section 4) and four stale ledger consumer records are noted (4.9). Still OPEN in this row: R22, the NOX_ realization lines and PCXD hand-model classes awaiting classification (4.8), and the Pool (the devnet Pool ran ELF 121f3e29…, not the frozen e0e49c34…).
10. **Trust inventory.** Section 4 matches the final closure one-to-one. Every row has its removal condition, and the 36 unnamed reviewed-transcription items have per-item conditions. Every row added under the standing delegation has been reported to the owner. Any row the owner has not confirmed is identified.
   *Status 2026-11-10: NOT MET.* Section 4 is now reconciled one-to-one against the replayed cones (NPI_). It gives a removal condition for every reached row and for each of the 36 unnamed reviewed-transcription items, keeps UNREACHED rows marked, lists PROPOSED rows separately, and records the owner status of each row from C3-BIN. It remains NOT MET until:
   1. the owner confirms or rejects RuntimeClockSlotBinding, RuntimeReturnDataClear, RuntimeEntrypointAdmission-Pool, RuntimeCpiAccountView, FixturePdaRuntime and the lead-added ReviewedTranscription items;
   2. each PROPOSED row of 4.8 is classified;
11. **Pool boundary.** Owner decision (aj)(a) is recorded. Then either the Pool consumer association is proved into the game, or the claim's first sentence names the condition.
12. **K086.** Exclusion or reachability is recorded, or the claim states the residual liveness caveat.
13. **Campaign accounting.** The multi-attempt reduction of section 3.5 is reviewed, or proved, or the claim is restricted to per-attempt wording.
14. **Frozen pins.** crates/, programs/r1-cost-probe and Cargo.lock are byte-identical to 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. The Pool is at b936275465600469312d1f058cdc91ea2a11f3dc with ELF e0e49c34…09dc. Any source change carries an invalidation assessment (AGENTS.md section 6).
15. **Toolchain consistency.** The stand-ins were compiled at Lean 4.31.0 and the DGP mirror and earlier headline work at 4.32.0. The final host build names one pinned toolchain and recompiles the stand-ins under it.

16. **Overflow semantics (R22).** The deployed ELFs wrap while the gate's emitted bodies are checked (section 4.4, CheckedVsWrapping). Before "established": the R22 audit of the final closure shows every reached cone TOTAL or its caller precondition proved, or the owner records R22 as a retained trust row and the claim's first sentence names it.

## 7. Uncertainties and findings from drafting

These are stated so that the published version does not inherit them silently.

1. **(CLOSED 2026-11-09, run 7.)** **Closing 12 rows does not assemble the top.** Ten top obligations are OPEN and eight are CANDIDATE (section 1.2.3). The largest are A1 (op10 current-body transport, INP estimate 30-55 scopes), NMF_B cut production (15-30), A2 (10-18) and HeadlineB (6-12, no module yet). The claim's timing should be stated in terms of these, not the row count.
2. **ExecB placement.** TAS_TopB's `ExecB.Fixed` docstring puts `admission1/2` among the oracle-free binders. Their types mention `e1`/`e2`, which under condition (4) are the adversary's outputs at H, so they cannot be oracle-free. DGP_ found the same defect for `sha256 p1 hashv syscall` and `missing`. The fix is to move them to the per-world block, which keeps the quantifier strength because World binders may depend on H. The host build must do this; the stand-in docstring is wrong as written.
3. **Q is counted on a⊤.** Under RZ-STATE, `queries` bounds the issued list of `a⊤`, not of `a`. Where `a` would output state `false`, the wrapper fails before the native call, so `a⊤` can issue more verifier calls than `a`. The published Q must be described as `a⊤`'s count. This draft does not see a soundness problem in that, but the wording matters.
4. **`missing`.** `NND_Missing.instance`, the term TAS names, was never delivered. The intended instance is INP's `missingLit`, which depends on the per-world env. NNH_ run 5 preflight P1 (RSL.Env has exactly four fields) passed according to the merge message. The literal instance is still to be built.
5. **The failure event's witness side.** `failureModel`'s per-run failure is "accepted and the extractor returns `none`". This draft did not re-audit how the extracted witness is tied to the spend relation (the Claims conjuncts, `F3X_ModelClaims`). The final statement audit must confirm it before the claim is described as "acceptance implies a valid spend witness except with probability total(Q)".
6. **Campaign accounting.** Stand-in theorem compiled (MAT_); host obligations H-MA1-3 open; phase factor c = 2; owner decision on publishing the campaign corollary in verifier-call-charged units (section 3.5).
7. **Pool enters through `TraceRep`.** Even on the verifier side, the theorem assumes the recorded non-verifier actions are what Pool and runtime did. Until (aj)(a) is decided, the honest wording is "conditional on the recorded Pool and runtime actions in the lineage".
8. **Ledger inconsistency (RESOLVED in ledger30, NNN_: NKB-F1 marked RESOLVED by NKL-RT-batch_tree).** NNK_LEDGER.json `open_findings` listed NKB-F1 against TX1:083 and TX2:055 with status OPEN, and the (bc) extraction reclassification record says "NKT-F1 batch_tree: TX1:083/TX2:055 remain OPEN". Both rows have status CLOSED in the same ledger, via NKL-RT-batch_tree. This is probably a stale carried text, but it must be reconciled before the gate.
9. **D188-P2.** The 2026-10-27 caveat qualifies deployed attribution at five retired-preparation interfaces (dot_type, prepared_claim, query_geometry, tx1, tx1_finish). Later work replaced much of that route with direct native bridges (amendment 2026-10-27 third) and ReviewedTranscription-prepared_claim. This draft did not confirm that every one of the five is now covered by a CLOSED bridge row. The final audit must.
10. **Missing removal conditions.** S2TrustedSdkBorrow, TrustedStd, RuntimeEntrypointAdmission, RuntimePersistence, RuntimeSha256Value, NativeContractSemanticTransport and 36 reviewed-transcription items have no recorded removal condition.

11. **Checked versus wrapping arithmetic was absent from this draft until 2026-11-09.** Stream C's provenance campaign (P0 pilot, P2a) found that fresh extractions of the frozen source differ from the gate on arithmetic (for example `M31::neg` as `P - self` checked in the gate versus wrapping in a fresh emission) because the historical extractions ran with overflow checks on and the deployed SBF build does not. The gate is a faithful extraction of the frozen source under that configuration, so provenance is restored by re-extracting with the recorded configuration; the semantic transfer to the wrapping binary is the pre-existing R22 obligation (C3-BIN addenda 2026-10-21 00:25, 01:00, 01:15), now listed in sections 4.4 and 6.

12. **Run 7 interface notes (2026-11-09).**
   - (a) `RSL.TASB.fail_sub_rec` is stated over the pre-(bu) interface: it takes `nmn` and `NNE_EntryRep`, which ruling (bu) dropped. The condition-(4) inclusion `NNH8_Outer.inclusion` (used by `AspisR1.NNH8_DeployedOuter`, `TAS_FinalB.fail_sub_rec` and `deployed_charge`) is the same two-line proof, `rcases` on the `.2.2` conjunct of the top, applied to `NNT_TopL.top_splitB_physical`. `RSL.TASB.fail_sub_rec` itself is not in the cone. `RSL.EVB.no_second_charge` is. The lead or owner should confirm that this restatement satisfies the section-1 wording.
   - (b) Non-vacuity is only definitional so far (section 6, row 5). A witness of `Runs` needs an actual recorded accepted tx1/tx2 pair.
   - (c) As in run 6, `deployed_charge` gives two separate facts. The first is the pointwise envelope of the World-dependent failure indicator by one fixed recorder program's event. The second is that program's mean bound. It does not state an expectation of the failure indicator as a program mean.

13. **Provenance snapshot 2026-11-09 (Stream C P6 snapshot, evidence/prov-p6s-20261109).** In the deployed_splitB cone, 258 of 1,612 annotated emitted definitions are RECEIPTED (reproduced from an archived input with pinned tools), 435 are EQUALITY_PROVED against a fresh extraction in the correct configuration, 4 EQUALITY_DOMAIN and 915 OPEN (547 without a correct-configuration fresh emission yet, 247 proved only against the wrong overflow configuration and so counted OPEN, 81 failed, 40 unrecorded). Of the 599 CLOSED rows, 471 are provenance-conditional and 114 provenance-clean at the annotated-definition level. 26 cone modules were extracted from a non-frozen source revision (for example AspisR72Sampler.Funs from field.rs blob a47a9996, whose M31.mul body differs from frozen 4bb3b3f); each needs a fresh-extraction equality or a domain equality before the row credit it carries is unconditional. The R22 packet pins frozen source b2727acd rather than 4bb3b3f and must be reconciled. Gate row 7 is therefore OPEN with these numbers; the complete P6 (after P1f/P2g/P3) is expected to reduce them.

14c. **Provenance refresh 3 and two corrections (Stream C P6u, 2026-11-10, evidence/prov-p6u-20261110).** (i) The source_revision field of 535 provenance records had been a fixed default string; 393 claimed the frozen source without support. RECEIPTED means only that the emission's source hash appears in some pin file or receipt of some revision, not pin-equality. Of the 256 RECEIPTED definitions in the cone, 35 have pin-equal evidence and 38 (SelectedMaskProbe) a separate fresh-equality record; 183 have neither. The honest cone count is therefore 993 settled (920 proved + 35 + 38) and 649 not settled (183 + 466 open) until the receipted extractions' revision and overflow configuration are re-derived. (ii) The deployed-body equalities (P3m-P3r) were compiled against the L187 replayed closure while the campaign's combined root PRVCmb_ROOT is built on the ledger30 gate chain; NHT_Constants and CurrentCompactCallerModelV1 are different objects under the same name in the two, and the NOC_*/NNH_HostSeed modules exist only in the L187 closure. Lead decision: the release universe is the L187 replayed closure; every credited provenance equality is to be replayed against it before being cited, and the final combined provenance root is built there; rows whose roots cite the other version of those two modules are to be listed and checked against the L187 reachable lists.

14b. **Provenance refresh 2 (Stream C P6t, 2026-11-10, evidence/prov-p6t-20261110).** Cone: EQUALITY_PROVED 920, RECEIPTED 256, EQUALITY_DOMAIN 6, CONDITIONAL_ON_BINDING 43, DEPENDS_ON_LIBRARY_TRUST 7 (each naming its trust row), HAND_ADAPTED 5, NO_FROZEN_COUNTERPART 4, OPEN 466 (263 without a correct-configuration emission, 17 wrong-basis). Rows: 180 clean, 405 conditional. Combined import: 4,812 theorems audited, standard axioms. All six top verifier bodies (stage1_owned, stage2_owned, candidate prepare/tx1, tx2_common/tx2_authenticated, the PublicPreparation transcript) now have fresh-extraction equalities parametric in their callees with the hypotheses shown satisfiable; discharging the callee bindings against the deployed operations is the next round. The public_bytes accessor is covered by the lead-added reviewed transcription (section 4.7a).

14a. **Provenance refresh (Stream C P6r, 2026-11-10, evidence/prov-p6r-20261110).** After two further equality rounds: EQUALITY_PROVED 848 (61 of them constructor-wise isomorphisms of Types declarations, flagged), RECEIPTED 256, EQUALITY_DOMAIN 6, CONDITIONAL_ON_BINDING 6, HAND_ADAPTED 33, NO_FROZEN_COUNTERPART 4, OPEN 554 (325 without a correct-configuration fresh emission, 172 failed, 40 unrecorded, 17 wrong-basis). Rows: 163 clean, 422 conditional (row tables committed, PCXD_ROW_TABLES.json). Combined import of 251 credited files: 2,472 theorems, standard axioms only. The campaign is stopped pending the owner decisions listed in item 14; the remaining OPEN set is dominated by tool limits (no fresh emission) and those decisions.

14. **Complete provenance pass (Stream C P6, 2026-11-10, evidence/prov-p6c-20261109).** In the deployed_splitB cone (209 emitted gate modules, 1,707 annotated definitions): RECEIPTED 256, EQUALITY_PROVED 694, EQUALITY_DOMAIN 6, CONDITIONAL_ON_BINDING 6, HAND_ADAPTED 33, NO_FROZEN_COUNTERPART 4, OPEN 708 (325 without a fresh emission, mostly tool limits; 224 failed; 119 wrong-basis; 40 unrecorded). Rows: 138 of 599 provenance-clean at the annotated-definition level, 447 conditional. The campaign's one combined import (PRVCmb_ROOT, 200 credited files, 2,121 theorems audited one by one, standard axioms) passes. The only genuine gate-versus-frozen difference found (transport row loop shifts) is proved unreachable (row equal on all arguments; loop equal for range end ≤ 16); the ShrAmt shift-amount bridge is verified for the overflow-checks-off configuration (NPE_, 2026-11-10). Open owner decisions: reconstruct versus re-route for 24 + 26 cut modules with no recovered source; trust-row classes for the hand-written SDK type and slice-iterator models and one cross-crate constant-encoding line; 8 gate-only helpers with no frozen counterpart. Gate row 7 remains OPEN; closing it needs those decisions plus further equality rounds, not only more of the same jobs.

15. **Cached-closure coherence (L187, 2026-11-10).** Lean does not re-typecheck imported objects, and neither the axiom walk nor the NFX scan detects an object compiled against a different version of an import. The cold replay found 56 such modules in the cached run-7 closure (L187_STALE_IMPORTS.json is a lower bound where receipts pinned direct imports only); three of their proofs no longer elaborated against the loaded definitions and were repaired proof-only with statements frozen; the constants that differed are outside both top theorems' cones. Gate row 3's credit therefore rests on the replayed closure, not on the cached objects.

16. **"599 CLOSED" is not "599 rows the proof uses" (NPI_ finding F1, 2026-11-10).**
   - Of the 599 CLOSED rows, 140 have a root in the cones of `deployed_splitB` and `deployed_charge`.
   - 7 more (TX1:330, TX1:333, TX1:344, TX2:213, TX2:221, TX2:240, TX2:241) enter through restated top fields (`NVR_TAS.*`, `NVR_TasRoots.*`, `NNT_Field.r241`).
   - The remaining 450 are proved statements about the same code that this theorem does not depend on. Two further rows, TX1:059 and TX2:040, record no root at all (NKT-F3).
   - Nothing is contradicted. For most rows, the CLOSED certificate is evidence that the Lean models describe the frozen code, not a premise the kernel checks for this theorem. The published claim must not present the row count as the size of the proof's dependency.

17. **Reviewed-transcription entries outside the cones (NPI_ finding F2, SETTLED 2026-11-10, NPI_L005).** 28 of the 37 inventory entries of 4.6 have no certificate root in the cones. For each one we checked whether a model in the cones is defined from the entry's certificate, or whether the certificate is proved about such a model.
   - **15 feed an installed model and are therefore reached trust.**
     - NJY-RT149/152/153/201/203: the host's installed adapter slots op31, op32, op48 and op49 are defined from the NJQ_ reference models through `NND_DecoderSlots.install`.
     - NKL-RT084: the cone's `LIBC_CanonicalScan` child is defined from `NKL_Checks.checks`.
     - NJZ-RT189, NKM-RTNGB002/004/006, NKI-RT233, NKY-RT216/218/235 and NKR-RT-218: their certificates are stated about the cone's own models.
   - **13 feed nothing in the cones:** NJZ-RT201 to 204, the five NKJ items, and NKR-RT-220/225/250/251.
   - For NKR-RT-250/251, the certificate explicitly does not equate its reference with the cone's old `FIq_Native…public_digest_lanes`. The model the cone uses for that function therefore takes its link to the frozen code from extraction (D188) and provenance (gate row 7), not from this certificate.
   - Section 4.6 marks each entry accordingly.

18. **One Rust model (owner decision 2026-11-10).** The soundness and privacy theorems were found to share only the mathematical core (R0C field, R0P Poseidon and protocol mathematics, SpendRelation, the sampler extraction) and to use different, unrelated constants for the verifier predicate, statement types and prover (evidence/model-intersection-20261110). The owner ruled that the single Rust model for both is the source that ran on devnet: 4bb3b3f (crates incl. aspis-prover, r1-cost-probe, Cargo.lock) and the Pool at b936275. Soundness is already at that pin; the privacy side regenerates its prover extraction and deployed models from it and re-proves its top over the soundness gate's verifier constants (or a model proved equal). The proving client that produced the devnet proofs is established (evidence/prover-client-20261110, evidence/client-repro-20261110): devnet_spend sha256 77e7e541… was built from tools/r1-cost-probe at dfa35acd (tree 82699657), rustc 1.94.1, `--release --locked --offline --features r1p-check`, with aspis-prover's insecure-spend-fixture feature hard-coded on, linking crates/ (identical to 4bb3b3f), programs/aspis-registry and the 4bb3b3f Pool tree (480e2c48, not b936275's), and it has been rebuilt byte-for-byte on the host at the original absolute path. The library crates that produced the proofs are therefore the pin's; the client wrapper, its feature set and the Pool library it linked are not, and the pin description must name them (owner decision pending: amend the pin, or rebuild the client from the pin with the production feature set and re-run devnet).

19. **Host re-instantiated at the deployed program ids (2026-11-10, evidence/host-ids-20261110).** The host under TAS_FinalB used CPH_Program.verifier = the July 2026 V7 devnet program id and LIB_Instances.D = placeholder pool/registry ids, so the model rejected every recorded R1 run (non-vacuity scoping, finding F1). A dependency walk over the replayed closure found 718 of 146,554 reachable constants depending on the three id constants; all were cloned with the 10 November deployment's ids (verifier GqZzWuGT…, pool 37hdATMk…, registry program 9pWwAcBg…, unchanged across both deployments) and sent to the kernel with full checking: 717 re-check with their original proofs (the ids are passed through), one (CPH_Program.not_system, a first-byte comparison) restated. The id-comparing ledger rows (TX2:234, TX1:345) were proved for arbitrary ids. Delivered: NPO_Nov.AspisR1.TAS_FinalB.deployed_splitB, deployed_charge, fail_sub_rec, NPO_Nov.AspisR1.NNH8_DeployedOuter at NPO_Nov.AspisR1.NOC_Run5bHost.S_host, kernel statements identical to section 1.2.2 modulo the host constants whose definitions differ only in the ids, standard axioms by the pinned walker; a second instance NPO_Oct at the 29 October ids (D = LIB_Deployed.devnet by rfl). The release instance is the 10 November one; a readable restatement module and an independent leanchecker replay are pending; the executable acceptance check on the recorded bytes needs a computable host instance (the host's sdk and references are noncomputable), which is now the first step of the row-5 witness.

Target not yet established.
