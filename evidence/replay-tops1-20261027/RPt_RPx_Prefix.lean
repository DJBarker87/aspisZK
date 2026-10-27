import RPt_RPx_Accounting
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_Prefix
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open DrvC_Installation F3T_ByteCarrier

/-- Every source occurrence has its original position and answer in the
account, even on rejection. No deduplication or permutation of this log. -/
theorem occurrences {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (P : ByteProver) (H : Bytes → State) :
    ∃ suffix : List (Bytes × State),
      (eval H (F3X_Account.program c hashv P)).1 =
        (eval H P).1 ++
        (eval H (F3T_Installed.source c hashv (input c (eval H P).2))).1 ++ suffix := by
  rw [F3X_Account.output]
  unfold F3X_Account.submitted
  rw [eval_bind]
  dsimp only
  split
  · rw [eval_bind]
    exact ⟨(eval H (F3X_Preparation.program c (eval H P).2)).1,by
      simp only [eval,List.append_nil,List.append_assoc]⟩
  · exact ⟨[],by simp only [eval,List.append_nil]⟩

/-- The account recorder returns the same complete attempted view, including
all rejected prefixes, before its audit and replay suffix. -/
theorem recorded {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (P : ByteProver)
    (select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (H : Bytes → State) :
    (eval H (Hiq_RecordedJoint.program (F3X_Account.program c hashv P)
      F3X_Projection.project select)).2 = eval H (F3X_Account.program c hashv P) :=
  Hiq_RecordedJoint.source_view _ _ _ H

#print axioms occurrences
#print axioms recorded
end AspisR1.RPx_Prefix
end
