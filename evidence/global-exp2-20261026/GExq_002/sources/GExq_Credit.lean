import GExp_CountLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_Credit
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def credit {A : Type} (n : Nat) (c : A → Nat) (p : Code A) : Prop :=
  ∀ H : Bytes → State, (eval H (SdkC_Oracle.program p)).1.length +
    (match (eval H (SdkC_Oracle.program p)).2 with | .ok a => c a | _ => 0) ≤ n

theorem pure_credit {A : Type} (n : Nat) (c : A → Nat) (a : A) (h : c a ≤ n) :
    credit n c (.done a) := by intro H; simpa only [SdkC_Oracle.program,eval,List.length_nil,Nat.zero_add] using h

theorem lift_credit {A : Type} (n : Nat) (c : A → Nat) (r : Result A)
    (h : ∀ a, c a ≤ n) : credit n c (liftResult r) := by
  intro H; cases r with
  | ok a => simpa only [liftResult,SdkC_Oracle.program,eval,List.length_nil,Nat.zero_add] using h a
  | fail e => exact Nat.zero_le _
  | div => exact Nat.zero_le _

theorem lift_bind_credit {A B : Type} (r : Result A) (k : A → Code B) (n : Nat)
    (c : B → Nat) (hk : ∀ a, credit n c (k a)) :
    credit n c (CheckpointBytes5Effect.bind (liftResult r) k) := by
  intro H; cases r with
  | ok a => exact hk a H
  | fail e => exact Nat.zero_le _
  | div => exact Nat.zero_le _

theorem bind_credit {A B : Type} (p : Code A) (k : A → Code B) (n m : Nat)
    (c : B → Nat) (hp : GExp_CountLaws.count n p) (hk : ∀ a, credit m c (k a)) :
    credit (n+m) c (CheckpointBytes5Effect.bind p k) := by
  intro H
  rw [GExp_IdealValue.bind_program,eval_bind]
  cases called : (eval H (SdkC_Oracle.program p)).2 with
  | ok a =>
    simpa only [called,List.length_append,Nat.add_assoc] using Nat.add_le_add (hp H) (hk a H)
  | fail e =>
    simpa only [called,eval,List.append_nil,Nat.add_zero] using (hp H).trans (Nat.le_add_right n m)
  | div =>
    simpa only [called,eval,List.append_nil,Nat.add_zero] using (hp H).trans (Nat.le_add_right n m)

theorem then_credit {A B : Type} {p : Code A} {k : A → Code B} {total cost : Nat}
    (c : B → Nat) (covered : cost ≤ total) (hp : GExp_CountLaws.count cost p)
    (hk : ∀ a, credit (total-cost) c (k a)) :
    credit total c (CheckpointBytes5Effect.bind p k) := by
  have h := bind_credit p k cost (total-cost) c hp hk
  have same : cost+(total-cost)=total := by omega
  simpa only [same] using h

#print axioms pure_credit
#print axioms lift_credit
#print axioms lift_bind_credit
#print axioms bind_credit
#print axioms then_credit
end AspisR1.GExq_Credit
end
