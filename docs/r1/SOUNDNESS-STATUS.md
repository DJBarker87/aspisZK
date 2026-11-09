# R1 soundness status

This is the status document for the soundness of the R1 spend path, and it is the one place where every figure and every caveat in the top-level README can be traced. It is reproduced without change from the research branch at commit `07123926e88273271344977a3fdc26d1780cde14`, where it lives as `docs/research/100bit-spend-path-20261013/design/SOUNDNESS-CLAIM-DRAFT-20261108.md`; only the headings have been moved down one level so that it sits under this title. It was written as the draft of the claim to be published once the release target is met, which is why it still calls itself a draft and why its own basis line names an earlier commit; its sections 0, 1.2.2, 1.3, 1.4 and 6 were brought up to date on 9 November 2026 with the compiled top-level theorems, and those are the parts the README relies on. It keeps the internal names of theorems, rulings and ledger items, because they are the references a reviewer needs to find the Lean source. The release target it describes, 100-bit classical per-attempt soundness for the actual frozen spend path, is not yet established; section 6 lists, gate by gate, what has been done and what remains, and [`OPEN-GATES.md`](OPEN-GATES.md) restates the open gates in plain terms.

---

## Soundness claim for the R1 verifier spend path (draft)

**Status: DRAFT. Target not yet established.** This document is the text Stream A intends to publish when the soundness target is met. Until every item in section 6 has evidence, the word "established" must not be applied to anything in it, and every heading below is read as "intended claim", not as a result. The draft changes no proof, ledger row, trust row, contract text or frozen source.

Basis for this draft: `research` at def3eee1fa1. Sources read:

- design/SECURITY-CONTRACT-20261021.md and its amendments of 2026-10-26, 2026-10-27 (three), 2026-10-28 (fourth, fifth, standing delegation) and 2026-11-09;
- C3-BIN-20261021.md, rulings (bc), (bk) with its addendum, (bm) to (bt), the owner decisions of 2026-11-07 (split top, option B with Realizes, binding conditions, RZ-STATE) and of 2026-11-08 (condition (4) by pointwise inclusion);
- evidence/top-assembly-20261107 (TAS_TopB.lean, TAS_TopB_NNE.lean, TAS_Interfaces.lean, TAS_G0_BRIEF.md), evidence/top-form-20261107 (TFM_TopExact.lean, TFM_REPORT.md), evidence/event-b-20261107 (EVB_REPORT.md, EVB_range.py), evidence/int-plan-20261107 (INP_REPORT.md), evidence/digest-p2-20261108 (DGP_DECISION.md);
- evidence/ledger27-20261111 (NNK_HANDOFF.md, NNK_REMAINING.md, NNK_TOP_COMPOSITION.json, NNK_TRUST_ADDITIONS.json, NNK_LEDGER_DELTA.json, NNK_K086.json, NNK_LEDGER.json.xz);
- design/TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md;
- evidence/replay-deployed2-20261027/RPx_Deployed.lean (the adopted headline) and lean/F3T_Numeric.lean, lean/F3U_Range.lean, lean/F3U_RangeMaximal.lean, lean/F3U_RangeEdges.lean.

Where this draft reconstructs a statement that has not been compiled, it says so. The published version must replace every reconstruction with the kernel statement printed from the compiled theorem.

### 0. Current position in one paragraph

*Updated 2026-11-09 after NNH_ run 7 (G0 FINAL), merged to `research` at 1133ee43a9f.* Ledger30 (NNN_) records 599 CLOSED, 0 QUALIFIED and 0 OPEN spend-path rows. The host top is assembled unconditionally at the corrected host `AspisR1.NOC_Run5bHost.S_host`. `AspisR1.TAS_FinalB.deployed_splitB` and `AspisR1.TAS_FinalB.deployed_charge` compile in `TAS_G0_COMBINED_IMPORT` with every interface field a delivered closed term. The three fields that were missing in run 6 are now filled: a1 := `AspisR1.NOQ_FinalCombined.field`, a2 := `AspisR1.NOF_A2FieldCorrected.field` and sp.rest := `AspisR1.NNH8_Rest.assemble`. TAS_G0_MISSING.json is empty. Condition (4) is proved under the section-1 rule as amended by ruling (bu) (section 7, item 12). G0 gate rows 1 to 4 of section 6 have their artifacts. Row 5 (non-vacuity) is partial, and release gates 5 to 16 are open. Extraction provenance (note (bk)) is still an unresolved release blocker.

### 1. The theorem as it will stand

#### 1.1 Precise prose

Fix the frozen verifier implementation (crates/, programs/r1-cost-probe and Cargo.lock at 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387) in the installed configuration `IDa_Deployed.deployedConfiguration missing indexError reservation`, with the owned TX1 and TX2 stage bodies taken at their AdapterRw models. Model SHA-256, as invoked through the runtime's hash syscall, as a uniformly random function H : Bytes → State. Let `a` be an arbitrary two-phase adaptive adversary (`SCE_Experiment.Adversary Bool`) and let `a⊤` be `a` with both of its allocator-state outputs replaced by `true`. Suppose that, for every oracle H, the digest queries issued by `a⊤` across both reached phases (`ARW_Induced.issued`, counting duplicates and every call issued before a rejection) number at most Q = Q0 + Q1.

For each H, let the deployed pair be what `a⊤` actually outputs at H: `⟨e1, data1, true⟩ := (eval H a⊤.first).2` and `⟨e2, data2, slot, true⟩ := (eval H (a⊤.second ⟨e1, data1, true⟩ saved post1 true)).2`. Suppose further that these two entries are executed by the Solana runtime as the approved two-transaction game: consecutive executions on one bank lineage, the same physical checkpoint account named by both with no intervening touch, TX1's parent status success, and the recorded checkpoint actions equal to the physical runtime actions (`Runs`: `frame`, `trace`, `ok1`, `out1`, `ok2`, `out2`), under the retained runtime, SDK and standard-library hypotheses.

Then three things hold (the first is H-free; the second and third hold at every H):

1. the numeric conjunct C5num of the adopted headline: `failureModel runtime ≤ total(Q)`, where `failureModel` is an average over H (bound-audit finding 3: it is not a per-H statement); if Q ≤ maxQueries then `failureModel runtime ≤ (Q+1)·2^-100`; and if Q = 0 then `failureModel runtime < 2^-100` with the exact margin;
2. the other conjuncts of `AspisR1.RPx_Deployed.deployed` except conjunct 4, unchanged (`Rest`: P6 boundary, driver and SDK equalities, the three Claims, copy facts, Rc2 events, CPH protection, trace and recorder facts, S6N installation);
3. either conjunct 4 holds with its internal bad event re-targeted to E_rec (`OutcomeRec`), or E_rec holds at H.

E_rec is the collision event already charged inside `failureModel`: `BinRawByteCollisionTargets.event` at Q + 2965 recorded reads on the adversary's own capped account run with the output-dependent selector `ARQ_Observer.select`.

Averaged over all H, with no conditioning and no H excluded, the per-attempt failure indicator `max r 1_{Runs ∧ ¬OutcomeRec}` has mean at most total(Q), with E_rec charged once. [Bound audit, 2026-11-08, finding 4: "charged once" is established in compiled Lean only for `failureModel`; for this per-attempt event including OutcomeRec it rests on the stand-in `RSL.EVB.no_second_charge` and a host theorem that is not yet compiled (section 1.2.2, G0 final). It is stated here as the target, not as a fact.] Here `r` is the per-world loss whose mean is `failureModel`, namely the extractor-failure mass of the accepted run (`RawRecordedOracleExtractionMassBin.failureMass`: the run is accepted and `RawRecordedPublicSpendExtractorBin.extract` returns `none`) plus the query-scan term.

#### 1.2 Lean form

##### 1.2.1 Compiled stand-in (exists)

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

##### 1.2.2 Host theorems (compiled; printed kernel statements)

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

##### 1.2.3 Interface fields that must be closed terms

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

#### 1.3 Every instantiated binder

Each of these is a substitution of a universally quantified headline binder, proved by `rfl` or by a named lemma. None is a hypothesis, and none is a trust row.

| Binder of RPx_Deployed.deployed | Instantiated as | Authority | Why it is not a restriction |
|---|---|---|---|
| `native1`, `native2` | `stage1_owned`/`stage2_owned (DrvC_Installation.sdk cfg)`, the AdapterRw models | owner decision 2026-11-07; TAS `Sig.model1/2` | The actual code meets the models only through the RSL rows plus A1/A2; `extraction` at native := model then holds by `rfl` (A0) except digestSource, which (bt) supplies. |
| `A`, `allocator`, `state1`, `final1`, `state2`, `final2` | `Bool`, `abortIndicator`, all `true` | ruling (bo); TFM `Alloc` | A returned-Ok actual run had every allocation succeed, since a failed allocation aborts the program. `Alloc.allocator_part` gives the allocator half of accepted1/2 at `true`. |
| `a` (in the pair and in `queries`) | `a⊤ := NNH_StateNormalize.normalize a` | owner decision 2026-11-07 (RZ-STATE) | The allocator state models allocation success, which the deployed attacker does not control. `a` itself stays universally quantified. |
| `e1 data1 state1`, `e2 data2 slot state2` | the outputs of `eval H a⊤.first` and `eval H (a⊤.second …)` | owner condition (4) | Realizes holds by construction at every H. Instantiating `a` to a constant adversary is forbidden. |
| `hashv`, `sha256`, `p1`, `syscall` | `hashAdapter H`, `H`, `⟨fun _ => rfl⟩`, `DGP_HostDigest.syscall` | ruling (bt); DGP_DECISION option (a) | `total_syscall_unique`: the adapter is the only total hashv the RuntimeSyscall row admits. Every consumed run returned, so the model agrees with the runtime on every consumed run. |
| `missing` | `NOC_HostCtx.missingLit c := NNH_Tx2Configuration.select (NNH_CorrectConfiguration.residual (NOC_HostSeed.m0 (envOf c).reservation) (envOf c)) (envOf c)` | ruling (s); INP section 1.6; host-model correction 2026-11-09 | Substitution of a universal binder. The seed is `NNH_HostSeed.m0` with current op1 := `NOC_HostSeed.filled` (heap::filled at 4bb3b3f, under the existing allocator trust row). The old seed left op1 as `.div`, so the old host never accepted a tx1 (NOC_PrepareDiv). `NOC_SeedTransfer` proves by rfl that only current op1 and sdk op10 change. This is a model correction under AGENTS section 4, with one slot and no contract or trust change. |
| `extraction`, `accepted1`, `accepted2`, `game` | derived, no longer binders | TAS/TFM/EVB | Derived from the row roots, A0 to A5 and `Runs`. |
| `alloc1` (TX1 window allocation stream) | `AspisR1.NNG_Candidate344.allocation` | AMEND item 7 (finding NNH-G0-F3) | Statement data fixed by ledger30's FIN entry, never a hypothesis. alloc2, allocation217, allocation234 and `ch` stay universally quantified. |
| `admission1`, `admission2`, `RuntimePersistence` | conjuncts of `run.frame` = GameFrame ∧ `NOC_Run5bHost.retained` | NFB_ admission grouping | They are no longer separate binders. They are the same trust rows, stated as facts of the actual run's world (section 1.4). |

#### 1.4 Every retained hypothesis

| Hypothesis | Kind | Notes |
|---|---|---|
| `queries` (L154) | statement parameter | Classified as the Q of the bound (amendment 2026-10-27 second, item 2). It is not discharged. It is taken on `a⊤`. |
| `Runs.frame` | game (a)-(c) plus the two non-trace equalities of (d), conjoined with `NOC_Run5bHost.retained` (admission1, admission2, RuntimePersistence) | Statement of the approved two-transaction game (amendment 2026-10-26 item 2), not an attacker restriction. `NNH8_NonVacuity.frame_recorded` gives its exact unfolding by `Iff.rfl`. |
| `Runs.trace` (`TraceRep`) | physical trace association, game (d) | Every `.invoke` action of `p.actions t/u` was executed as `entry` at the RSL images, and every non-verifier action is the recorded Pool or runtime action. This hypothesis is where Pool behaviour enters the theorem (section 5). |
| `Runs.ok1`, `Runs.ok2`, `Runs.out1`, `Runs.out2` | the attack's success antecedent | Both actual entries returned Ok, with their recorded outputs. |
| `admission1`, `admission2` | trust (RuntimeEntrypointAdmission) | Now conjuncts of `run.frame` (not separate binders). |
| `RuntimePersistence` | trust | Now a conjunct of `run.frame` (`CPR_DataPersistence.TwoTransactionLaw`). |
| `sdk : S2TrustedSdkBorrow L` | trust | |
| `std : TrustedStd copy` | trust | W1 qualification retained. |
| `count1`, `count2` (3 and 7 accounts) | host facts, not hypotheses | `NNE_EntryArgs.count`. |
| `alloc2` (and the TX2:217/234 allocation streams, `ch`) | universally quantified data | Allocation-success streams for the (bn) windows and leaf rows; no allocator-success trust item (NNK_HANDOFF). `alloc1` is instantiated (section 1.3). |
| `fx`, `w`, `H` (and `wOf`, `anchor` in deployed_charge) | universal | `fx.a` is an arbitrary adaptive adversary, never constant. `anchor` is fixed program data, not a condition on the sampled oracle. |

The final theorem must contain no Root0 hypothesis, no hash-injectivity premise, no Realizes premise and no new trust row. The G0 gate (TAS_G0_BRIEF section 7, item 4) requires a written confirmation of each. **Confirmed at run 7** (TAS_G0_AUDIT.json `written_confirmations`):

- There are zero Root0, Realizes and injectivity tokens in the printed statements, and no new trust row.
- `realizes_mk` is the eval-of-map lemma.
- `exhibited_mk` = `rfl`, `eventRec_mk` = `Iff.rfl` and `queries_mk` = `fun _ _ H _ _ h => h H`, each checked by an rfl example. `queries_mk` is the forall-world L154 family, not literally `id`.
- `a` is universal.
- The averaging conditions on nothing.

### 2. Before and after, against the adopted headline

The format follows AGENTS.md section 3. "Before" is `AspisR1.RPx_Deployed.deployed` (kernel statement SHA-256 8ae0107f9dbb7374135912ff9dda3597ad0096023d0deed471b0cd4dcf305523, adopted 2026-10-27). "After" is the split-B host theorem of section 1.2.2.

**Quantifiers.**
- Before: every binder is independent and universal, including the deployed pair `e1 e2 data1 data2 slot state1 state2`, the adversary `a`, `native1 native2`, `allocator`, `hashv sha256 p1 syscall` and `missing`. The pair is not tied to `a`. The only link is `queries`, which bounds `a`'s issued list (EVB section 1.4).
- After: `a` stays universal. The pair is no longer quantified: it is defined as `a⊤`'s execution output at H. `native1/2`, `allocator`, the four states, `hashv/sha256/p1/syscall` and `missing` are instantiated (section 1.3). The per-world binders (`saved post1 post2 p t u actions RuntimePersistence w1 w2 admission1/2`) stay universal and may depend on H arbitrarily (`wOf`).
- Net effect: the new theorem covers fewer free instantiations of model-side binders, and every one of them is justified as a substitution in section 1.3. It covers the adaptive case that the old theorem did not connect to the bound: a pair chosen after querying H is a charged part of `a`. At each H, every pair the old statement covered is also covered, because a constant adversary realizes it with zero queries. The universal statement, however, is a different theorem, not a weakening, because the pair is now bound to the adversary's run. The owner approved this change on 2026-11-07.

**Carriers.** Unchanged: the Aeneas carriers `S2W_ExtractionBoundary.First/Second`, `Slice U8`, `Heap (Nat → Record)`, `Bytes → State`. `A` becomes `Bool`. The RSL carriers (`TX2_240.Args`, `SdkState`, `Env`, `Obs`) are added on the actual-code side and are related to the headline carriers by `EnvRep`, `args1/2`, `state1/2` and `Out1/2`.

**Hypotheses removed or added.**
- Derived instead of assumed: `extraction`, `accepted1`, `accepted2`, `game`.
- Added: `Runs` (frame, trace, ok1, out1, ok2, out2), the actual-run antecedent. `game` was itself a binder before, so this is a re-expression of game (a)-(d) on the actual RSL images plus the actual Ok results, not a new kind of assumption. The earlier `realizes` hypothesis approved on 2026-11-07 is discharged by construction and does not appear.
- Unchanged: `queries`, both admissions, `RuntimePersistence`, `sdk`, `std`, `copy`.
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

### 3. The numeric claim

#### 3.1 The exact bound

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

#### 3.2 Per-attempt corollary and its valid range

`F3U_Range.per_attempt`: for Q ≤ maxQueries, total(Q) ≤ (Q+1)·2^-100, where

maxQueries = `F3U_RangeEdges.maxQueries` = 7388980242446479800895501321004157112314840375 ≈ 2^152.372.

`F3U_RangeMaximal.exact_range` proves the converse: total(Q) ≤ (Q+1)·2^-100 holds if and only if Q ≤ maxQueries. Above maxQueries the bound total(Q) still holds, but the (Q+1)·2^-100 form does not. EVB_range.py reproduces maxQueries from exact rationals. Owner decision 2026-11-07: under option B the number and the range are unchanged. Option A would have needed a second accountLoss, with range ≈ 2^151.787, and is not used.

(Q+1)·2^-100 is a corollary of total(Q), not the contract (contract 2026-10-21, "Correction to the lead's adoption addendum"). The binding criteria are (A) and (B) of the contract, stated here as follows.

- **(A), whole experiment with no adversary queries.** `F3T_Numeric.margin_exact`:
  2^-100 − total(0) = 2^-108 − 6·(1161² + 2965²)/2^256 − 2^-126 − 2^-454 > 0.
  Numerically, total(0) = 510/2^109 + 60834876/2^256 + 2^-126 + 2^-454 ≈ 0.99609·2^-100 ≈ 2^-100.0056. The margin is ≈ 0.999996·2^-108. The 2^-100 target is met at Q = 0 with about 2^-108 to spare, and almost all of total(0) is the 34 transcript starts.
- **(B), Q-dependence kept.** For 0 ≤ Q ≤ maxQueries, the failure probability is at most total(Q), which is approximately (Q+34)·2^-105.093 for every Q below about 2^100. The (Q+1)·2^-100 figure is looser than total(Q) by a factor of 2^5.093 (= log2(512/15)) for Q above about 10^4; the factor is about 2^4.9 only near Q ≈ 233 (bound audit, finding 1).

No proof-of-work or grinding credit is used. No probability is divided by adversarial work, and this draft states no work-normalised figure.

#### 3.3 Query accounting

- What is counted: `ARW_Induced.issued model1 copy abortIndicator CPH_Program.verifier a⊤ H`, the chronological list of digest calls the induced prover issues across both phases. This includes duplicate queries and every call before a rejection. It is identified with `(eval H P).1.length` by `ARW_Induced.queries` (amendment 2026-10-27, item 1).
- What the verifier adds: the constants 34 (starts), 1161 (distinct first reads), 1921 (first-read budget on the account run) and 2965 (recorded reads for E_rec) are verifier envelopes, charged on top of Q. The issued-call log is at most Q+2322.
- What the attacker's adaptive pair choice costs: under Realizes the pair is the output of `a⊤`, so every query used to choose it is in Q.

#### 3.4 Why adaptive selection is covered

Before option B, the charged event in conjunct 4 used a constant selector on a pair quantified independently of `a`. If the pair may be an arbitrary function of H, the probability of that event can be 1 (EVB section 3, a pigeonhole argument, not Lean-checked). Option B removes this gap by construction:

1. The pair is `a⊤`'s output at H.
2. E_rec is evaluated on `a⊤`'s own account run with the output-dependent selector `ARQ_Observer.select`.
3. `F3T_AccountCharge.bound`, the account-mass lemma, holds for any selector applied to the source's own output, and `FJp_Mass` already charges it as accountLoss(Q).
4. `fail_sub_rec` proves that at every H, a successful actual run whose OutcomeRec fails lies in E_rec at the same H.

The inclusion is proved, not assumed (owner condition (2)), and it concerns the actual adversary's execution (owner decision 2026-11-08, item (1)).

#### 3.5 Repeated attempts

**Within one experiment.** Repeats are covered. `queries` counts every issued call, including duplicates and rejected prefixes, across both phases. An adversary that tries many candidate transcripts offline before submitting is charged for every query it makes. That is the ROM work metric of the contract.

**Across separately submitted spend attempts.** No theorem in the dependency closure states a multi-attempt bound. The contract amendment of 2026-10-27 (second, item 2) says such campaigns are "accounted for by the per-attempt bound exactly as in the 2026-10-21 contract", and that contract gives the per-experiment form (B). The drafter's reduction is the following. It is not Lean-checked and must be reviewed or proved before publication.

1. For k submitted attempts against the same oracle, attempt i is an instance of the theorem with the adversary a_i that runs everything up to and including attempt i.
2. The world binders are arbitrary, so earlier chain state is covered.
3. a_i must reproduce the verifier's digest calls of earlier attempts as its own queries, at most 2322 per attempt.
4. A union bound then gives Pr[some attempt accepted with failure] ≤ Σ_{i=1..k} total(Q_i). MAT_ (evidence/multi-attempt-20261108, stand-in theorem `RSL.MAT.campaign_charge`/`campaign_bound`, compiled, standard axioms) corrects this sketch: Q_i is the CUMULATIVE issued-call count of the reduction adversary a_i, Q_i ≤ c·(Q_adv,≤i + 2322·(i−1)), with phase factor c = 2 for the current two-phase adversary type (the second phase recomputes the first, `SCE_Experiment.Adversary` carries no private state); c = 1 would need a host argument. Its host obligations H-MA1 (construction of a_i with the submitted inputs as its outputs at every H), H-MA2 (its cost) and H-MA3 (whatever the campaign adversary sees between attempts is a function of H and oracle-free data fixed before H, so a_i can recompute it with charged queries) are not discharged. LEAD READING, 2026-11-08, for the owner: H-MA3 does not restrict what the attacker may observe or adapt to; it is a cost-accounting rule that charges the verifier's digest calls of earlier attempts (2322 each) to the reduction adversary's query count. That is exactly the "work performed through verifier interactions" item the security contract must state explicitly (AGENTS.md section 1); whether the campaign corollary is published in these units, or campaign security stays stated per attempt only, is an owner decision on contract scope, not a proof question.

This sum is not to be replaced by setting a single-experiment bound to 1 (AGENTS.md section 2). If the lead does not accept the reduction, the published claim must say that campaign security is stated per attempt only.

#### 3.6 What the number applies to

The number bounds the per-attempt failure of the two-transaction spend experiment: the attack succeeds at H and either the extractor fails or OutcomeRec fails. It applies under the trust inventory of section 4, at the frozen source and configuration of section 1.1. It is not a statement about privacy, Pool settlement, double spending, custody or availability (section 5).

### 4. Trust inventory the theorem relies on

Authority: design/TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md, as approved 2026-10-27 and amended since, and the 25 trust rows plus the reviewed-transcription inventory in NNK_LEDGER.json (ledger27). "Used" names the consumer in the top or in CLOSED rows. Where the inventory records no removal condition, the table says so. That gap is itself a finding (section 7).

#### 4.1 Oracle and cryptographic model

| Row | Assumes | Used | Removal condition |
|---|---|---|---|
| Random-oracle model for SHA-256 (frozen3 security/oracle model, L194) | SHA-256 as invoked through the runtime behaves as a uniformly random function H; every probability is over H. | Every probability statement: failureModel, E_rec, deployed_charge. | None. A standard-model argument would be a different theorem. |
| P1 ideal-oracle realization (`S2W_ExtractionBoundary.P1.realization`: ∀ bytes, sha256 bytes = H bytes) | The fixed native digest equals the sampled oracle at the supplied world. This is not a proof that SHA-256 is random. | After (bt), instantiated per world (`sha256 := H`, `p1 := rfl`). The row remains the justification for reading the physical hash replies in `Runs` as H's values. | None. Inherent to the ROM reading. |
| RuntimeSyscall.returningValue | Successful returning digests satisfy `hashv parts = ok d → decodeState d = sha256 (flatten parts)`. No totality or termination is assumed. | After (bt), a theorem at `hashAdapter` (`DGP_HostDigest.syscall`). The row justifies the physical reading of every returned hash in `Runs`. | A proved realization of the pinned runtime's hash syscall. Not recorded in the inventory. |
| RuntimeSha256Value | The SolanaDigest/hashv reply value realises H. Exact request slices and unchanged reply are separate bridge obligations. | Retained-value uses at TX1:327, TX2:210. | None recorded. |

#### 4.2 Solana runtime behaviour (owner decision 2026-11-04)

| Row | Assumes | Used | Removal condition |
|---|---|---|---|
| RuntimeEntrypointAdmission (verifier; 7 fields plus 2 wrapper fields) | Initial heap validity, fresh guards, zero counters and external borrows, live accounts, key/cell alias consistency at the two entries. | `admission1`, `admission2` (retained hypotheses). | None recorded. |
| RuntimePersistence (`CPR_DataPersistence.TwoTransactionLaw`) | For the next transaction on the same bank lineage loading an ordinary account, data bytes equal the previous transaction's final bytes if its parent succeeded, else its starting bytes. Zero lamports means absent. Data bytes only. | Retained hypothesis. Consumed by game (b) and the persisted cut field of NMF_B (INP section 1.3). | None recorded. |
| Allocator (data-only interface) | `allocate/cleanup` operations, with no success proposition. | Instantiated at `abortIndicator` by (bo). Physical justification: a failed allocation aborts the program, so a returned-Ok run had none. That reading falls under the AllocatorABICompilerSourceToELF realization obligation below. | Not applicable as a free binder after (bo). |
| RuntimeReturnData (nonempty, 1 ≤ len ≤ 1024) | `set_return_data(b)` followed by an immediate `get_return_data()` with no intervening CPI returns `Some((P, b))`. | One CLOSED native use (`emit_result`). Pool-side association OPEN. | None recorded. |
| RuntimeReturnDataClear | An empty `set_return_data` clears observable return data until a later set, within one instruction. | Window law of TX2:240 stage2. No CLOSED use yet. | A proved realization of the pinned runtime's return-data register. |
| RuntimeMemcmp | `sol_memcmp_` on the same two valid 688-byte ranges: normal return, slot zero iff equal, no other effect. | scan_proof_buffer, one direct CLOSED row. | Trust-reduction packet on the pinned validator implementation (not commissioned). |
| RuntimeClockSlotBinding (ADDED-LEAD-20261105) | `clockGet ctx = ok v → v = bankSlot ctx` in the same instruction context. Nothing about success, monotonicity or epochs. | `Clock::get()` in owned stage2 (r1_pool_adapter_owned.rs:479); NNE_Clock; the (bn) window NMV_WindowClock. | A proved realization of the pinned Clock sysvar. |
| RuntimeCpiAccountView (Stream C, ADDED-LEAD-20261110) | One returning Pool CPI: unlisted admitted accounts unchanged; listed ones reflect the callee's final values. | Pool CPI sites only. No CLOSED use. Relevant only if Pool execution enters the claim. | A proved realization of the deployed runtime's CPI account update. |
| RuntimeEntrypointAdmission-Pool | The same seven fields at the Pool entrypoint. | No CLOSED verifier row. | None recorded. |
| RuntimeCpiReadonlyEntry7 | Pending, unused. | Not relied on. | — |
| FixturePdaRuntime | PDA syscall agrees with the guarded model for seven fixture invocations. | Non-vacuity witness only. Never used by the soundness theorem. | — |

#### 4.3 Translation, tool and library trust

| Row | Assumes | Used | Removal condition |
|---|---|---|---|
| **Extraction item** (AeneasExtraction, D188), at trace fidelity, narrowed by D188-P3 and by **(bc)** | Trace fidelity: the pinned Charon/Aeneas translation of each associated frozen body preserves the accepted Result and the chronological attempted digest-call sequence, with rejected prefixes both rejecting. Narrowing (D188-P3): bodies that fail the dropped-restoration scan or native differential get no credit and are bridged natively. Narrowing (bc): "faithful except explicit returns or `?` in post-loop code merged into a loop exit; every emitted body relied on must be shown free of that pattern, or the affected exits certified natively." | Every CLOSED row on the emitted-body route. Under (bm), increased reliance for the emitted bodies of TX1:136, 137, 087 and TX2:234 (NNI/NNK extraction reclassifications). At the top, `extraction` at native := model holds by `rfl`, so the trust sits in the per-row emitted-body theorems. | For the tool, none. For release, every reached emission must be reproduced from an archived input, or re-extracted with per-definition equality theorems (note (bk)). |
| P6 / Kani association, with the K-1 narrowing (2026-10-28) and (br) scope | Pinned Kani/CBMC as evidence for checked associations between the frozen body and its reference. Credit only without copy builtins, or with the KMX element-wise copy stubs (sha256 bcdf749b…a9a67) and a matched failing negative control. Timeouts earn nothing. | Native halves of the hybrid rows. TX2:217 contracts under (br). | None for the tool. |
| NativeContractSemanticTransport (amendment fifth) | Kani's and Aeneas's interpretations of the enumerated frozen bodies and references denote the same Rust semantics under the certified common world. Also covers the recorded association of the Rust entries with `native1/native2`, the digest wrapper with `op43`, and the external digest with `hashv`. | 380 direct CLOSED rows; NLT-TX2:065; NMN-TX2:064. | None recorded. Clarification of P6/D188, not a removal. |
| P7 compiler, LLVM, platform and release-pinned library base | The selected compiler/toolchain/ABI and the pinned Lean/Mathlib/Aeneas base, for the exact recorded source, features and toolchain. | Whole closure. | None for the tool. Source-to-ELF association is a separate obligation (L188). |
| AllocatorABICompilerSourceToELF | Retained realization boundary: concrete final-artifact binding. | Root realization. | "RETAINED ROOT REALIZATION OBLIGATION". Discharged only by L188. |
| S2TrustedSdkBorrow (15 fields; solana-account-info 2.3.0) | Documented data-borrow and RefCell guard semantics. No caller result. | `sdk` binder; the (bn) window laws. | None recorded. |
| TrustedStd (`slice_copy_from_slice`, `option_ok_or`, `result_unwrap32`) | Pinned std semantics on valid references. W1: the abstract law quantifies all states, so each actual use needs justified validity. | `std` binder; std windows. | None recorded. W1 must be met at each use. |
| **CheckedVsWrapping (R22, OPEN)** | The gate's emitted bodies are Aeneas translations compiled with overflow checks ON (historical extraction configuration `CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true`, `RUSTFLAGS=-C overflow-checks=yes`), so every integer operation is checked and an overflow is an error result. The deployed R1 ELFs were built by cargo-build-sbf with the plain release profile (receipts `evidence/finish-pair2-20261027/FJd_SBF_default.json`, `FJd_SBF_devnet.json`; the frozen Cargo.toml enables overflow-checks only for aspis-r1-cert-check and aspis-r1-cert-build), so the deployed code WRAPS. The theorem is about the checked semantics; its transfer to the deployed binary needs, on every reached path, either totality (no checked operation fails, so both semantics agree: `R22TotalCheckedComposition`) or the direction wrapping-acceptance implies checked-acceptance with the same result. Status per `design/R22-TOTAL-20261021.md`: general lemma proved; 35 cones TOTAL, 63 ACCEPTED-ONLY (caller precondition still owed), 48 OTHER; global R22 OPEN. | Every CLOSED row on the emitted-body route, through the source-to-ELF association (L188). | Discharged by the R22 totality audit closing on the final closure (every reached cone TOTAL or its precondition established by the caller join), or stated as a retained trust row by the owner. Recorded here 2026-11-09 after Stream C's provenance campaign found the configuration difference (checked gate versus wrapping fresh emissions). |
| Standard logical axioms | `propext`, `Classical.choice`, `Quot.sound` only, for each new top and audited root. | Kernel. | None. F-AXIOM: 105 nonstandard imported axioms are unreachable from the tops and are not premises, but strict import-wide standard-only still fails. |

#### 4.4 Reviewed transcriptions (class ReviewedTranscription; P6/D188 option-A reclassification, never removal)

Named rows the brief singles out:

| Row | Assumes | Used | Removal condition |
|---|---|---|---|
| ReviewedTranscription-TX1:344 ((bn), ADDED-LEAD-20261107) | The listed textual substitution in the source-fission copy of `r1_pool_adapter_owned.rs::stage1` (fission sha256 9824c8ff…ebbf; NMV_fission.py, NMV_ASSOCIATIONS.json) preserves the frozen body's behaviour. | `NMV_CandidateRoots.root344` / `NMV_TasRoots.field344`. Unused by CLOSED rows today; becomes consumed when TX1:344 closes. | A native certificate on the actual frozen function. |
| ReviewedTranscription-TX2:240 ((bn), ADDED-LEAD-20261107) | The same, for `stage2`. | `NMV_CandidateRoots.root240` / `field240`. Unused by CLOSED rows today. | The same. |
| ReviewedTranscription-TX2:217 ((ah), ADDED-LEAD-20261107) | The reviewed safe `NCV_reference.rs::decode_lane_ref`, with the segment associations of NMX_217_NATIVE_COMPOSITION.md, preserves the frozen `decode_lane_from_pool_release` behaviour on every input; the final Box allocation admits return or silent abort. | CLOSED TX2:217 (`NMX_R3_DecoderFold.root`). | A native certificate on the actual frozen function, paired with the same emitted reference, without reviewed-transcription reliance. |
| ReviewedTranscription-prepared_claim ((ah)) | Hand transcription of f_ref, tied to the frozen function by Kani proof_for_contract. | TX1:193, 179, 186. | An emitted body proved equal to the transcription. |
| ReviewedTranscription-queries_from_pairs ((ah)) | Reviewed transcription of the reference. | TX1:168; TRANSCRIPT.actual_queries; TX1:179/186. | The same. |
| ReviewedTranscription-polynomial ((ah)) | NHE reverse-fold transcription. | One CLOSED row. | Not recorded in the ledger row. |
| NKL-RT-batch_tree ((bc)(4)) | Transcription of explicit-Result f_ref with native segment contracts at every exit. | TX1:081-083, TX2:053-055. | Not recorded in the ledger row. |
| Pool rows POOL324, POOL345, POOL296, POOL320, POOL223, POOL332 (Stream C, ADDED-LEAD-20261110) | Source-fission or hand-composition transcriptions of Pool functions (details in the appendix). | Pool rows only; 0 direct verifier CLOSED rows. Listed because the theorem's `TraceRep` names Pool actions, and because these rows would enter if (aj)(a) puts Pool execution inside the game. | A native certificate on the actual frozen function, or an emitted body proved equal. |

The ledger lists 36 further verifier-side items, each consumed by the named CLOSED row: NJY-RT149/152/153/201/203 (TX2:149, 152, 153, 201, 203); NJZ-RT189/201/202/203/204 (TX1:189, 201-204); NKJ-RT036/044/040/041/043; NKM-RTNGB002/004/006; NKI-RT234/260/233; NKL-RT084; NKU-RT124 (TX2:124); NKY-RT235/216/218 (TX1:235, TX2:216, TX2:218); NKR-RT-225/232/251/250/220/218; NLH-RT-261/237/263/256. The ledger records no per-item removal condition for any of these. The class default under (ah) is "an emitted body from the pinned extractor (or an approved successor) proved equal to the transcription". The published inventory must state a removal condition per item.

#### 4.5 Not trust, but stated parts of the theorem

These are listed so they are not mistaken for discharged assumptions:

- the query budget L154 (a statement parameter);
- the two-transaction game (a)-(d) in `Runs.frame/trace` (classified G, a statement of the experiment);
- the actual-run antecedent `Runs.ok1/ok2/out1/out2`;
- the allocation streams `alloc1/alloc2`.

The seven historical checkpoint interfaces (`S2X.CheckpointVersionBinding.*`, `…history`) are not relied on (appendix, "no additional trust").

### 5. What is explicitly NOT claimed

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

### 6. Gate evidence required before "established" may be used

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
5. **Non-vacuity.** For an arbitrary actual run, a `World` and the `Runs` facts are constructed from a recorded trace, showing `TraceRep` and `GameFrame` are the physical facts and not `False` (TAS_WIRING item 8).
   *Status 2026-11-09: PARTIAL.* `NNH8_NonVacuity` (NNH_L941) proves several things: `worldOf` builds a World from recorded data; GameFrame, Game, TraceRep and Out1 are, by `Iff.rfl`, the recorded CPG/CPH/trace and carrier facts rather than `False`; Out1 is inhabited; and Exhibited, EnvRep and Realizes hold at every world. No `Runs` inhabitant has yet been constructed from an actual recorded accepted deployed pair (section 7, item 12).
6. **Averaging obligations.** DGP O1 (recorder at `hashAdapter H` equals recorder at a fixed returning hashv) and O2 (recorder independent of the env's sha256 at missingLit) are proved, or a failure is reported. The same-recorder `rfl` (INP section 1.7) is checked.
7. **Extraction provenance.** Every emission reached by a credited root is reproduced from an archived input with the pinned tools, or re-extracted with per-definition equality theorems (note (bk)). The provenance status line reads zero unreproduced blobs reached.
8. **Coherent cold replay (L187)** of the final dependency closure, in the pinned workspace, under capped scopes. Not cached imports.
9. **Final audit (L188).** Trust and axiom audit of the final closure, together with the source-to-ELF association for the release verifier ELFs (f8c0ec72… and 63ad3e9c…, or newly reproduced pins), including the AllocatorABICompilerSourceToELF realization.
10. **Trust inventory.** Section 4 matches the final closure one-to-one. Every row has its removal condition, and the 36 unnamed reviewed-transcription items have per-item conditions. Every row added under the standing delegation has been reported to the owner. Any row the owner has not confirmed is identified.
11. **Pool boundary.** Owner decision (aj)(a) is recorded. Then either the Pool consumer association is proved into the game, or the claim's first sentence names the condition.
12. **K086.** Exclusion or reachability is recorded, or the claim states the residual liveness caveat.
13. **Campaign accounting.** The multi-attempt reduction of section 3.5 is reviewed, or proved, or the claim is restricted to per-attempt wording.
14. **Frozen pins.** crates/, programs/r1-cost-probe and Cargo.lock are byte-identical to 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. The Pool is at b936275465600469312d1f058cdc91ea2a11f3dc with ELF e0e49c34…09dc. Any source change carries an invalidation assessment (AGENTS.md section 6).
15. **Toolchain consistency.** The stand-ins were compiled at Lean 4.31.0 and the DGP mirror and earlier headline work at 4.32.0. The final host build names one pinned toolchain and recompiles the stand-ins under it.

16. **Overflow semantics (R22).** The deployed ELFs wrap while the gate's emitted bodies are checked (section 4.3, CheckedVsWrapping). Before "established": the R22 audit of the final closure shows every reached cone TOTAL or its caller precondition proved, or the owner records R22 as a retained trust row and the claim's first sentence names it.

### 7. Uncertainties and findings from drafting

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

11. **Checked versus wrapping arithmetic was absent from this draft until 2026-11-09.** Stream C's provenance campaign (P0 pilot, P2a) found that fresh extractions of the frozen source differ from the gate on arithmetic (for example `M31::neg` as `P - self` checked in the gate versus wrapping in a fresh emission) because the historical extractions ran with overflow checks on and the deployed SBF build does not. The gate is a faithful extraction of the frozen source under that configuration, so provenance is restored by re-extracting with the recorded configuration; the semantic transfer to the wrapping binary is the pre-existing R22 obligation (C3-BIN addenda 2026-10-21 00:25, 01:00, 01:15), now listed in sections 4.3 and 6.

12. **Run 7 interface notes (2026-11-09).**
   - (a) `RSL.TASB.fail_sub_rec` is stated over the pre-(bu) interface: it takes `nmn` and `NNE_EntryRep`, which ruling (bu) dropped. The condition-(4) inclusion `NNH8_Outer.inclusion` (used by `AspisR1.NNH8_DeployedOuter`, `TAS_FinalB.fail_sub_rec` and `deployed_charge`) is the same two-line proof, `rcases` on the `.2.2` conjunct of the top, applied to `NNT_TopL.top_splitB_physical`. `RSL.TASB.fail_sub_rec` itself is not in the cone. `RSL.EVB.no_second_charge` is. The lead or owner should confirm that this restatement satisfies the section-1 wording.
   - (b) Non-vacuity is only definitional so far (section 6, row 5). A witness of `Runs` needs an actual recorded accepted tx1/tx2 pair.
   - (c) As in run 6, `deployed_charge` gives two separate facts. The first is the pointwise envelope of the World-dependent failure indicator by one fixed recorder program's event. The second is that program's mean bound. It does not state an expectation of the failure indicator as a program mean.

Target not yet established.
