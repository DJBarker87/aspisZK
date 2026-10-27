import FJh_Base
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJh_InternalRoundModel
open FJh_Base (Exact)
theorem update (s : Fin 16 → Exact) (c : Exact) :
    Function.update s (0 : Fin 16) ((s 0+c)^5)=
      (fun j : Fin 16=>if j=0 then R0P.poseidonPow5 (s 0+c) else s j) := by
  funext j
  by_cases h : j=0
  · subst j
    rw [Function.update_same,if_pos rfl]
    unfold R0P.poseidonPow5
    ring
  · rw [Function.update_of_ne h,if_neg h]
#print axioms update
end AspisR1.FJh_InternalRoundModel
end
