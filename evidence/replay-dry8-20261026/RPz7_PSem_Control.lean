import RPz7_PSem_Lenses
set_option autoImplicit false
namespace AspisR1.PSem_Control
open Aeneas Aeneas.Std Result

theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (m >>= k)=ok v) : ∃ x,m=ok x ∧ k x=ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => cases h
  | div => cases h

theorem pair_success {α β γ : Type} (m : Result (α × β))
    (k : α → β → Result γ) (v : γ)
    (h : (do let (a,b) ← m; k a b)=ok v) :
    ∃ a b,m=ok (a,b) ∧ k a b=ok v := by
  cases m with
  | ok pair => cases pair with | mk a b => exact ⟨a,b,rfl,h⟩
  | fail e => cases h
  | div => cases h

theorem add_value (a b c : Usize) (h : a+b=ok c) : c.val=a.val+b.val := by
  have facts := UScalar.add_equiv a b
  rw [h] at facts
  exact facts.2.1

theorem div_two (a b : Usize) (h : a/2#usize=ok b) : b.val=a.val/2 := by
  obtain ⟨b',call,value⟩ := UScalar.div_spec a (y:=2#usize) (by scalar_tac)
  have same := Result.ok.inj (call.symm.trans h)
  subst b'
  exact value

theorem loop_success {α β : Type} (body : α → Result (ControlFlow α β))
    (state : α) (out : β) (call : loop body state=ok out) :
    ∃ r, body state=ok r ∧
      match r with | .cont next => loop body next=ok out | .done value => value=out := by
  unfold loop at call
  cases step : body state with
  | fail error => simp only [step,bind_tc_fail] at call;cases call
  | div => simp only [step,bind_tc_div] at call;cases call
  | ok r =>
    refine ⟨r,rfl,?_⟩
    rw [step] at call
    cases r with
    | cont next => exact call
    | done value => exact Result.ok.inj call

#print axioms bind_success
#print axioms pair_success
#print axioms add_value
#print axioms div_two
#print axioms loop_success
end AspisR1.PSem_Control
