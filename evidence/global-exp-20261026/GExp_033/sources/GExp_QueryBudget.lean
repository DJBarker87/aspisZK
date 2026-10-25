import GExp_InstalledPrepare
import S1CurrentPrepareBudgetV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_QueryBudget
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open CheckpointBytes5Effect (Code)

def bounded {A : Type} : Nat → Code A → Prop
  | _, .done _ => True
  | n, .step r k => match r with
    | .ok a => bounded n (k a)
    | .fail _ => True
    | .div => True
  | n, .read _ k => 0 < n ∧ ∀ a, bounded (n-1) (k a)

theorem lower_bounded {A : Type} (p : PreparedHashCode.Code A) (n : Nat)
    (h : PreparedBudget.bounded n p) : bounded n (SdkD_PrepareLower.lower p) := by
  induction p generalizing n with
  | done a => trivial
  | step r k ih => cases r with
    | ok a => exact ih a n (h a)
    | fail e => trivial
    | div => trivial
  | digest D hash parts k ih => exact ⟨h.1,fun a => ih a (n-1) (h.2 a)⟩

theorem program_count {A : Type} (p : Code A) (n : Nat) (h : bounded n p)
    (H : Bytes → State) : (eval H (SdkC_Oracle.program p)).1.length ≤ n := by
  induction p generalizing n with
  | done a => exact Nat.zero_le _
  | step r k ih => cases r with
    | ok a => exact ih a n h
    | fail e => exact Nat.zero_le _
    | div => exact Nat.zero_le _
  | read parts k ih =>
    have rest := ih (AspisV8R19.SqueezeOracleBridge.encodeState
      (H (AspisV8R19.SqueezeOracleBridge.flatten parts))) (n-1) (h.2 _)
    have positive := h.1
    simp only [SdkC_Oracle.program,eval,List.length_cons]
    omega

theorem attempted_count {A : Type} (p : Code A) (n : Nat) (h : bounded n p)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (before : SdkC_Source.Log) :
    (SdkC_Source.run hashv p before).2.length ≤ before.length + n := by
  induction p generalizing n before with
  | done a => exact Nat.le_add_right _ _
  | step r k ih => cases r with
    | ok a => exact ih a n h before
    | fail e => exact Nat.le_add_right _ _
    | div => exact Nat.le_add_right _ _
  | read parts k ih =>
    have positive := h.1
    cases call : hashv parts with
    | ok a =>
      have rest := ih a (n-1) (h.2 a) (before ++ [⟨parts,.ok a⟩])
      simp only [SdkC_Source.run,call,List.length_append,List.length_singleton] at rest ⊢
      omega
    | fail e =>
      simp only [SdkC_Source.run,call,List.length_append,List.length_singleton]
      omega
    | div =>
      simp only [SdkC_Source.run,call,List.length_append,List.length_singleton]
      omega

theorem prepare (ops : AspisR1CurrentCaller.Ops)
    (B : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : Hash)
    (input : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize) :
    bounded 115 (SdkD_PrepareLower.lower (SdkD_PrepareSource.code ops B std D pub proof hash input)) :=
  lower_bounded _ _ (AspisR1CurrentCaller.S1PrepareCode.prepare_bounded _ _ _ _ _ _ _ _)

#print axioms lower_bounded
#print axioms program_count
#print axioms attempted_count
#print axioms prepare
end AspisR1.GExp_QueryBudget
end
