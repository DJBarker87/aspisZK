import RPz7_GExp_Experiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_GlobalBudget
open Aeneas Aeneas.Std Result
open GExp_Experiment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem bind_length {A B : Type} (p : Program Bytes State A) (k : A → Program Bytes State B)
    (H : Bytes → State) (m n : Nat) (hp : (eval H p).1.length ≤ m)
    (hk : ∀ a, (eval H (k a)).1.length ≤ n) :
    (eval H (bind p k)).1.length ≤ m+n := by
  rw [eval_bind,List.length_append]
  exact Nat.add_le_add hp (hk _)

theorem budget (current : AspisR1CurrentCaller.Ops) (stage : VTop_Stages.Ops) (reserved : Bool)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D1 : AspisR1CurrentCaller.aspis_core.digest.Digest32 Unit)
    (D2 : VTop_Stages.aspis_core.digest.Digest32 Unit)
    (adversary : Program Bytes State FirstInputs)
    (chooseSecond : FirstInputs → alloc.vec.Vec U8 → Program Bytes State SecondInputs)
    (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H adversary).1.length ≤ Q0)
    (choiceBound : ∀ input saved H, (eval H (chooseSecond input saved)).1.length ≤ Q1)
    (H : Bytes → State) :
    (eval H (program current stage reserved B std hashv D1 D2 adversary chooseSecond)).1.length ≤
      Q0+Q1+22585 := by
  unfold program
  apply (bind_length _ _ H Q0 (11350+(Q1+11235)) (prefixBound H) ?_).trans
  · omega
  intro input
  apply bind_length _ _ H 11350 (Q1+11235)
  · exact GExp_FirstBudget.first _ _ _ _ _ _ _ _ _ H
  intro reply
  cases reply with
  | fail e => exact Nat.zero_le _
  | div => exact Nat.zero_le _
  | ok r => cases r with
    | Err e => exact Nat.zero_le _
    | Ok saved =>
      apply bind_length _ _ H Q1 11235 (choiceBound input saved H)
      intro next
      apply (bind_length _ _ H 11235 0 ?_ (fun _ => Nat.zero_le _)).trans
      · omega
      exact GExp_SecondBudget.second _ _ _ _ _ _ _ H

#print axioms bind_length
#print axioms budget
end AspisR1.GExp_GlobalBudget
end
