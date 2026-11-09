# The top-level R1 soundness theorems

Source: research commit `07123926e88273271344977a3fdc26d1780cde14`. The two statements below are copied character for character from `evidence/integrate-20261111/TAS_G0_AUDIT.json`, field `kernel_statements_verbatim`, which records the output of Lean with `set_option pp.all true` and `pp.proofs false` (compile attempt NNH_L941, 9 November 2026). The Lean source that proves them is [`TAS_FinalB.lean`](TAS_FinalB.lean), and the full audit record is [`TAS_G0_AUDIT.json`](TAS_G0_AUDIT.json), both copied here unchanged from the same directory.

The two theorems are `AspisR1.TAS_FinalB.deployed_splitB` and `AspisR1.TAS_FinalB.deployed_charge`. The first says what holds of a single run of the two-transaction spend at a fixed oracle; the second turns that into the averaged bound over a random oracle. Both are proved at the corrected host model of 9 November 2026, described at the end of this page, and both are about the frozen R1 source at revision `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. They are a real step, but they are not yet the release claim: the gates listed in [`OPEN-GATES.md`](OPEN-GATES.md) stand between them and it, and the security target is not yet established.

## `deployed_splitB`

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

### Reading the binders

`W` and `Tx` are the types of runtime worlds and of transactions. The theorem holds for every choice of them, so nothing about the shape of a Solana world or transaction is fixed beyond what the other binders say.

`L0` is the model of the Solana account-information library the verifier calls to borrow account data, and `borrow` is the trust row `S2TrustedSdkBorrow`, which states the documented borrowing and `RefCell` guard behaviour of `solana-account-info` 2.3.0. `copy` is the slice-copy operation on the heap, and `std` is the trust row `TrustedStd`, which states the pinned standard-library behaviour of `copy_from_slice` and of the small `Option` and `Result` helpers the code uses. These four are where the theorem relies on the SDK and the standard library; they are listed with their scope in [`TRUST-INVENTORY.md`](TRUST-INVENTORY.md).

`allocation217`, `allocation234`, `ch` and `alloc2` describe which heap allocations succeed during the second transaction: `allocation217` for `decode_lane_from_pool_release` (row TX2:217), `allocation234` for `authenticate_invariant_release_registry` (row TX2:234), `ch` for the three allocation decisions inside `authenticate_asq8_accounts` (row TX2:233; its fields are `sites`, `lane` and `registry`), and `alloc2` for the windows of the second stage. They are universally quantified, so the theorem holds whatever pattern of allocation success or failure occurs; a failed allocation aborts the program, and the theorem only speaks about runs that returned successfully. The allocation stream of the first stage is not a binder: it is fixed to `AspisR1.NNG_Candidate344.allocation` as part of the statement.

`fx` is the oracle-independent data of the experiment. Its most important field is `fx.a`, the adversary, which is an arbitrary two-phase adaptive program that may query the oracle as it likes before choosing the first transaction and again before choosing the second; it is never fixed to a particular strategy. The other fields of `fx` are the remaining inputs that do not depend on the oracle: the PDA derivation, the clock reply, the allocator reservation bit, the two query budgets `Q0` and `Q1` for the two phases, and fixed program data (an index-error code, a root and length, a prior program, transcript words and a decoder).

`w` is the per-world data: the two runtime worlds, the saved checkpoint bytes, the heaps after each stage, the bank observations, the two transactions themselves and the list of runtime actions. Because `w` is universally quantified it may depend on the oracle in any way, which is what lets the theorem cover every world the runtime could produce.

`H` is the random oracle, a function from byte strings to hash states. SHA-256, as the program calls it through the runtime's hash syscall, is modelled by `H`; every probability in the second theorem is over a uniformly random `H`.

`queries` is the query budget. It says that, for every oracle, the adversary issues at most `Q0 + Q1` digest queries across both phases, counting every repeated query and every query made before a rejection. It is taken on the adversary with its allocator outputs set to success, which is the adversary that actually reaches the verifier. This is the `Q` of the numeric bound; it is a parameter of the statement, not something assumed about the attacker's behaviour.

`run` is the description of the run itself, and it is where the two-transaction game enters. It says that the two transactions were executed by the runtime one after the other on one bank lineage, that both named the same checkpoint account and nothing else touched it in between, that the first transaction's parent status was success, that the recorded checkpoint actions are the physical runtime actions, and that both stages returned `Ok` with their recorded outputs. It also carries the two runtime trust rows `RuntimeEntrypointAdmission` and `RuntimePersistence`, and it is where the Pool enters: the theorem takes the recorded non-verifier actions in the lineage to be what the Pool and the runtime did.

### Reading the conclusion

The conclusion has three parts. The first, `Sig.Bound`, is the numeric statement `failureModel ≤ total(Q)` for this run's runtime image, with `total` the bound of [`SOUNDNESS-STATUS.md`](SOUNDNESS-STATUS.md), section 3. The second, `NNH8_Split.rest`, is every other conjunct of the adopted headline theorem `AspisR1.RPx_Deployed.deployed` except its fourth: the boundary, driver and SDK equalities, the three spend claims, the copy facts, the event facts, the checkpoint protection, the trace and recorder facts and the installation. The third is a disjunction: either the outcome conjunct holds with its bad event set to `E_rec`, or the run lies in `E_rec`, the collision event among the recorded hash reads of the adversary's own run, which is already paid for inside `total(Q)`.

## `deployed_charge`

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

### Reading the binders

`W`, `Tx`, `L0`, `borrow`, `copy`, `std`, `allocation217`, `allocation234`, `ch`, `alloc2`, `fx` and `queries` mean exactly what they mean above. There is no single world `w` and no single oracle `H`: instead `wOf` is an arbitrary function giving a world for each oracle, so the world may depend on the oracle in any way at all, and `anchor` is a fixed hash function used only as program data to build the one recorder program the event is evaluated on; it is not a condition on the sampled oracle.

### Reading the conclusion

The conclusion has three parts. The first says that, for every oracle, if the two transactions run as described and the outcome conjunct fails, then the recorder program `NNH8_RecorderFixed.fixedProgram copy fx anchor`, run against that oracle, lands in the collision event `BinRawByteCollisionTargets.event` at `Q0 + Q1 + 2965` recorded reads. The second says that the mean of that event's indicator over a lazily sampled random oracle, `lazyMean … FS.emptyTable …`, is at most `F3T_Numeric.total (Q0 + Q1)`. The third says that, for every oracle, `failureModel` of the run's runtime image is at most `total (Q0 + Q1)`. These are the two recorder facts and the model bound on which the averaged claim rests; the theorem states the pointwise domination and the mean bound separately, and it does not itself write the average of the failure indicator as a single program mean, which the status document records in section 7, item 12(c).

## Proof discipline

`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for both theorems, and for every field term installed in them (`AspisR1.NOQ_FinalCombined.field`, `AspisR1.NOF_A2FieldCorrected.field`, `AspisR1.NNH8_Rest.assemble`, `AspisR1.NNH8_NMF.nmfB`, `AspisR1.NNQ_HostDigest.o2`, `AspisR1.NNH_DigestSyntaxTransport.o1`); there is no `sorry`, no project-specific axiom and no `native_decide`. As an independent check on `#print axioms`, the proof terms were also walked directly by a separate pinned program (SHA-256 `46ee271b392729449147b978830b474e3fa4ecba2b45e03ad13c02490ba6ca3c`), which followed every edge from each root: it reached 146,370 constants over 6,981,053 edges from `deployed_splitB` and 146,551 constants over 6,993,492 edges from `deployed_charge`, and in each case the set of axioms it walked to equals the set Lean collects, namely the same three. A cross-reference scan of the whole closure, 20,019 modules and 883,431 declarations, found no dangling reference, no declaration owned twice and no import that differs from its recorded source (attempt NNH_L948, exit 0). The combined import that contains both theorems and all their fields compiled in 48.8 seconds with a peak resident memory of 6,881,368 KiB and no swap (attempt NNH_L945).

The audit also confirms in writing that the printed statements contain no hypothesis about the `Root0` digest, no hash-injectivity premise, no `Realizes` premise and no new trust row; that the adversary is universal and never a constant; and that the averaging conditions on nothing, so every oracle and every world counts with its full weight.

Lean checks these proofs about the model the statements name. That the extracted Lean definitions are faithful to the deployed program, that the deployed binary computes what the source says, and that the trust rows hold of the real runtime are separate matters, and they are the open gates.

## The host-model correction of 9 November

Until 9 November the model of the host environment left one operation, the zero-filled buffer allocation at the start of the first stage, as a placeholder that never returns. Lean proved that consequence directly (`NOC_PrepareDiv.op1_div`): under the old model the first transaction could never be accepted, so a top theorem stated there would have been vacuous for real runs. The corrected model installs the allocation as the frozen source writes it (`heap::filled` at `4bb3b3f`, which returns a zeroed vector when the reservation succeeds and an allocation error otherwise), under the existing allocator trust row, and `NOC_SeedTransfer` proves by `rfl` that only that operation and one SDK slot changed. No contract text and no trust row changed. Both theorems above are stated at the corrected host `AspisR1.NOC_Run5bHost.S_host`.
