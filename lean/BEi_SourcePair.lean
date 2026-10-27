import BEi_AcceptedCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEi_SourcePair
open Aeneas Aeneas.Std Result SdkC_Source BEi_Execution
open S2W_NativeConsolidation S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd S2Trust
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Reuses the SAME reached f/s source cuts and actual Prepared/root witnesses.
The operational executions are constructed, not requested as hypotheses.
The intervening history/state are explicit, since checkpoint and other
operations occur between the batches. Physical association is still separate. -/
theorem same_pair {S F : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (call : SdkC_Source.Parts → S → Result SdkC_Source.Digest × S)
    (binding : ∀ parts state, (call parts state).1 = hashv parts)
    (state state2 : S) (before between : SdkC_Source.Log)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (Op5T_SamePair.dictionary adapter ops stage finish B std) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (Op5T_SamePair.dictionary adapter ops stage finish B std) accounts1 accounts2 saved f s) :
    ∃ (p0 : AspisR1CurrentCaller.verifier.Prepared) (root0 : Array U8 32#usize)
      (p2 : VTop_Stages.verifier.Prepared) (root2 : Array U8 32#usize)
      (middle after : S) (log0 log1 : Log),
      SdkC_BatchPair.Returning hashv H (SdkC_BatchSource.currentCode hashv f.proof p0 root0) (.Ok ()) ∧
      SdkC_BatchPair.Returning hashv H (SdkC_BatchSource.stageCode hashv s.proof p2 root2) (.Ok ()) ∧
      Executes call (SdkC_BatchSource.currentCode hashv f.proof p0 root0)
        state before (.ok (.Ok ())) middle log0 ∧
      Executes call (SdkC_BatchSource.stageCode hashv s.proof p2 root2)
        state2 (log0 ++ between) (.ok (.Ok ())) after log1 ∧
      log0 = before ++ (SdkC_Source.run hashv (SdkC_BatchSource.currentCode hashv f.proof p0 root0) []).2 ∧
      log1 = (log0 ++ between) ++ (SdkC_Source.run hashv (SdkC_BatchSource.stageCode hashv s.proof p2 root2) []).2 := by
  obtain ⟨p0,root0,p2,root2,first,second⟩ := SdkC_BatchPair.same_pair adapter ops stage finish B std
    native1 native2 hashv extraction sha256 H p1 syscall accounts1 accounts2 saved f s cuts
  obtain ⟨middle,log0,steps0,logs0⟩ := BEi_AcceptedCut.construct call hashv binding _ _ first.1 state before
  obtain ⟨after,log1,steps1,logs1⟩ := BEi_AcceptedCut.construct call hashv binding _ _ second.1 state2 (log0 ++ between)
  exact ⟨p0,root0,p2,root2,middle,after,log0,log1,first,second,steps0,steps1,logs0,logs1⟩

#print axioms same_pair
end AspisR1.BEi_SourcePair
end
