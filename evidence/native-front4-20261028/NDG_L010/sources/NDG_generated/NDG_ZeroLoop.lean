import NDG_ErrorLaws
set_option autoImplicit false
namespace NDG_ZeroLoop
open Aeneas Aeneas.Std Result

theorem done {A B : Type} (body : A → Result (ControlFlow A B)) (x : A) (y : B)
    (step : body x=ok (.done y)) : loop body x=ok y := by
  conv_lhs => unfold loop
  simp only [step]

theorem cont {A B : Type} (body : A → Result (ControlFlow A B)) (x next : A)
    (step : body x=ok (.cont next)) : loop body x=loop body next := by
  conv_lhs => unfold loop
  simp only [step]

theorem wrapping_advance (i : Usize) (bound : i.val < 65536) :
    (Usize.wrapping_add i 1#usize).val = i.val + 1 := by
  simp only [UScalar.wrapping_add]
  scalar_tac

#print axioms done
#print axioms cont
#print axioms wrapping_advance
end NDG_ZeroLoop
