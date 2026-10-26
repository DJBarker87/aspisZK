import GExq_FirstBudget
import GExq_SecondBudget
import GExq_GlobalBudget
import F3T_ByteCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3X_SourceBudget
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open DrvC_Installation F3T_ByteCarrier

theorem pair {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) (H : Bytes → State) :
    (eval H (DrvC_PairProgram.source c hashv semantic pub proof)).1.length≤1921 := by
  unfold DrvC_PairProgram.source
  apply (GExq_GlobalBudget.bind_length _ _ H 1018 903 ?_ ?_).trans
  · omega
  · exact GExq_FirstBudget.first _ _ _ _ _ _ _ _ _ H
  · intro first
    cases first with
    | fail err => exact Nat.zero_le _
    | div => exact Nat.zero_le _
    | ok reply => cases reply with
      | Err err => exact Nat.zero_le _
      | Ok saved =>
        apply (GExq_GlobalBudget.bind_length _ _ H 903 0 ?_ (fun _=>Nat.zero_le _)).trans
        · omega
        · exact GExq_SecondBudget.second _ _ _ _ _ _ _ H

theorem source {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (s : Submission) (H : Bytes → State) :
    (eval H (F3T_Installed.source c hashv (input c s))).1.length≤1921 := by
  unfold F3T_Installed.source
  split
  · split
    · exact pair c hashv _ _ _ H
    · exact Nat.zero_le _
  · exact Nat.zero_le _

#print axioms pair
#print axioms source
end AspisR1.F3X_SourceBudget
end
