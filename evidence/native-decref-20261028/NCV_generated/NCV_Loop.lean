import NCV_Reference.Funs
set_option autoImplicit false
namespace NCV_Loop
open Aeneas Aeneas.Std Result

theorem done {A B : Type} (body : A → Result (ControlFlow A B)) (x : A) (y : B)
    (step : body x=ok (.done y)) : loop body x=ok y := by
  conv_lhs => unfold loop
  simp only [step]

theorem cont {A B : Type} (body : A → Result (ControlFlow A B)) (x next : A)
    (step : body x=ok (.cont next)) : loop body x=loop body next := by
  conv_lhs => unfold loop
  simp only [step]

theorem advance (i : Usize) (bound : i.val < 768) :
    ∃ next : Usize, i+1#usize=ok next ∧ next.val=i.val+1 := by
  have spec : (i+1#usize : Result Usize) ⦃ x => x.val=i.val+1 ⦄ := by
    apply UScalar.add_spec <;> scalar_tac
  exact WP.spec_imp_exists spec

#print axioms done
#print axioms cont
#print axioms advance
end NCV_Loop
