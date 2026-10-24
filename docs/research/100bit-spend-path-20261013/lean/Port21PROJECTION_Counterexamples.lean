import Port21PROJECTION_Core

/-! Small interface counterexamples, not claims about the production allocator. -/
set_option autoImplicit false
namespace AspisR1.Port21PROJECTION_Counterexamples
open AspisV8R19.MemoizedProgramLaw

def native : Program Bool Bool Bool :=
  .ask false fun b => if b then .done true else .ask true fun _ => .done false

def model : Program Bool Bool Bool := .ask false fun b => .done b

/-- Even accepted full-log equality and total output equality cannot supply
all-outcome accounting: a rejected native prefix may contain extra queries. -/
theorem same_output (H : Bool → Bool) : (eval H native).2 = (eval H model).2 := by
  cases h : H false <;> simp only [native,model,eval,h,Bool.false_eq_true,if_false,if_true]

theorem accepted_same_log (H : Bool → Bool) (accepted : (eval H native).2 = true) :
    (eval H native).1 = (eval H model).1 := by
  cases h : H false with
  | false => simp only [native,eval,h,Bool.false_eq_true,if_false] at accepted
  | true => simp only [native,model,eval,h,if_true]

theorem rejected_extra_queries :
    (eval (fun _ => false) native).2 = false ∧
    (eval (fun _ => false) native).1.length = 2 ∧
    (eval (fun _ => false) model).1.length = 1 := by
  exact ⟨rfl,rfl,rfl⟩

#print axioms same_output
#print axioms accepted_same_log
#print axioms rejected_extra_queries
end AspisR1.Port21PROJECTION_Counterexamples
