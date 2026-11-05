import NGU_Carriers
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace NGU_Loop
theorem done {S O : Type} (body : S → Result (ControlFlow S O)) (s : S) (out : O)
 (h : body s=ok (.done out)) : loop body s=ok out := by rw [loop.eq_def,h]

theorem cont {S O : Type} (body : S → Result (ControlFlow S O)) (s next : S)
 (h : body s=ok (.cont next)) : loop body s=loop body next := by rw [loop.eq_def,h]

#print axioms done
#print axioms cont
end NGU_Loop
