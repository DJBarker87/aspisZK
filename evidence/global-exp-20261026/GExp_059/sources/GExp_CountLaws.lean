import GExp_RowsBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_CountLaws
open Aeneas Aeneas.Std Result CheckpointBytes5Effect GExp_QueryBudget
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.MemoizedProgramLaw
open AspisV8R19.OracleProgramOps

def count {A : Type} (n : Nat) (p : Code A) : Prop :=
  ∀ H : Bytes → State, (eval H (SdkC_Oracle.program p)).1.length ≤ n

theorem of_bounded {A : Type} (p : Code A) (n : Nat) (h : bounded n p) : count n p :=
  fun H => program_count p n h H

theorem bind_count_on {A B : Type} (p : Code A) (k : A → Code B)
    (H : Bytes → State) (m n : Nat)
    (hp : (eval H (SdkC_Oracle.program p)).1.length ≤ m)
    (hk : ∀ a, (eval H (SdkC_Oracle.program p)).2 = .ok a →
      (eval H (SdkC_Oracle.program (k a))).1.length ≤ n) :
    (eval H (SdkC_Oracle.program (CheckpointBytes5Effect.bind p k))).1.length ≤ m+n := by
  rw [GExp_IdealValue.bind_program,eval_bind]
  cases called : (eval H (SdkC_Oracle.program p)).2 with
  | ok a => simpa only [called,List.length_append] using Nat.add_le_add hp (hk a called)
  | fail e => simpa only [called,eval,List.append_nil] using (hp.trans (Nat.le_add_right m n))
  | div => simpa only [called,eval,List.append_nil] using (hp.trans (Nat.le_add_right m n))

theorem bind_count {A B : Type} (p : Code A) (k : A → Code B) (m n : Nat)
    (hp : count m p) (hk : ∀ a, count n (k a)) :
    count (m+n) (CheckpointBytes5Effect.bind p k) := by
  intro H
  exact bind_count_on p k H m n (hp H) (fun a _ => hk a H)

theorem then_count {A B : Type} {p : Code A} {k : A → Code B} {total cost : Nat}
    (covered : cost ≤ total) (hp : count cost p)
    (hk : ∀ a, count (total-cost) (k a)) :
    count total (CheckpointBytes5Effect.bind p k) := by
  have h := bind_count p k cost (total-cost) hp hk
  have same : cost+(total-cost)=total := by omega
  simpa only [same] using h

theorem pure_count {A : Type} (n : Nat) (a : A) : count n (.done a) := fun _ => Nat.zero_le _

theorem lift_count {A : Type} (n : Nat) (r : Result A) : count n (liftResult r) :=
  of_bounded _ _ (lift_bound _ _)

theorem lift_bind_count {A B : Type} (r : Result A) (k : A → Code B) (n : Nat)
    (hk : ∀ a, count n (k a)) : count n (CheckpointBytes5Effect.bind (liftResult r) k) := by
  intro H
  cases r with
  | ok a => exact hk a H
  | fail e => exact Nat.zero_le _
  | div => exact Nat.zero_le _

#print axioms of_bounded
#print axioms bind_count_on
#print axioms bind_count
#print axioms then_count
#print axioms pure_count
#print axioms lift_count
#print axioms lift_bind_count
end AspisR1.GExp_CountLaws
end
