import NCV_ArrayFrame
set_option autoImplicit false
namespace NCV_ArrayRun
open Aeneas Aeneas.Std Result

theorem run {A B : Type} [Inhabited A] {n : Usize}
    (body : (Array A n × Usize) → Result (ControlFlow (Array A n × Usize) B))
    (target : Array A n) (finish : Array A n → B)
    (steps : ∀ (a : Array A n) (i : Usize), i.val<n.val → ∃ next : Usize, next.val=i.val+1 ∧
      body (a,i)=ok (.cont (a.set i (NCV_ArrayFrame.coord target i.val),next)))
    (terminal : ∀ (a : Array A n) (i : Usize), n.val ≤ i.val → body (a,i)=ok (.done (finish a)))
    (a : Array A n) (i : Usize) (bound : i.val ≤ n.val)
    (pre : NCV_ArrayFrame.Prefix a target i.val) :
    loop body (a,i)=ok (finish target) := by
  have all : ∀ k : Nat, ∀ (a : Array A n) (i : Usize), i.val ≤ n.val → n.val-i.val=k →
      NCV_ArrayFrame.Prefix a target i.val → loop body (a,i)=ok (finish target) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro a i hi hk pre
      by_cases done : n.val ≤ i.val
      · have eq : i.val=n.val := by omega
        have same : a=target := NCV_ArrayFrame.whole a target (by simpa only [eq] using pre)
        rw [NCV_Loop.done _ _ _ (terminal a i done),same]
      · have lt : i.val<n.val := by omega
        obtain ⟨next,value,step⟩:=steps a i lt
        rw [NCV_Loop.cont _ _ _ step]
        exact ih (n.val-next.val) (by omega) _ next (by omega) rfl
          (by simpa only [value] using NCV_ArrayFrame.extend a target i lt pre)
  exact all (n.val-i.val) a i bound rfl pre

#print axioms run
end NCV_ArrayRun
