import R1Z.PV_RDB2E_FallbackScalar

section
-- Unchanged source component R1Z.PV_CBL_FallbackRoundsModel
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackRoundsModel
open PV_CBL_FallbackScalar PV_CBL_FallbackArray4
set_option autoImplicit false
def run (s : State) (words : List U32) : State := words.foldl step s
theorem run_nil (s : State) : run s [] = s := rfl
theorem run_cons (s : State) (w : U32) (ws : List U32) :
    run s (w::ws) = run (step s w) ws := rfl
theorem run_append (s : State) (xs ys : List U32) :
    run s (xs++ys) = run (run s xs) ys := by
  exact List.foldl_append
theorem run_four (s : State) (a b c d : U32) :
    run s [a,b,c,d] = step (step (step (step s a) b) c) d := rfl
def packed (s : State) : A4 × A4 := (pack s.a s.b s.e s.f,pack s.c s.d s.g s.h)
#print axioms run
#print axioms run_nil
#print axioms run_cons
#print axioms run_append
#print axioms run_four
#print axioms packed
end R1Z.PV_CBL_FallbackRoundsModel

end
