import XSa_DotRun
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace XSa_LoopErrors

theorem failed {S O : Type} (body : S → Result (ControlFlow S O)) (s : S) (e : Error)
 (h : body s=fail e) : loop body s=fail e := by rw [loop.eq_def,h]

theorem diverged {S O : Type} (body : S → Result (ControlFlow S O)) (s : S)
 (h : body s=div) : loop body s=div := by rw [loop.eq_def,h]

#print axioms failed
#print axioms diverged
end XSa_LoopErrors
