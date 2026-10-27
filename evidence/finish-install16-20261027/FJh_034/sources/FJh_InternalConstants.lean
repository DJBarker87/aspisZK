import FJh_Base
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJh_InternalConstants
open Aeneas Aeneas.Std Result FIq_Native
open FJh_Base (cell P Exact)
def value (r : Fin 14) : U32 := cell poseidon2.INTERNAL r
theorem read (r : Usize) (hr : r.val<14) :
    Array.index_usize poseidon2.INTERNAL r=ok (value ⟨r.val,hr⟩) := by
  exact ExtractedMaskHornerStep.array_index_usize_ok _ r hr
theorem canonical (r : Fin 14) : (value r).val<P := by
  unfold value cell poseidon2.INTERNAL
  fin_cases r <;> decide
theorem model (r : Fin 14) : ((value r).val : Exact)=R0P.poseidonInternalConstants r := by
  unfold value cell poseidon2.INTERNAL R0P.poseidonInternalConstants
  fin_cases r <;> rfl
#print axioms read
#print axioms canonical
#print axioms model
end AspisR1.FJh_InternalConstants
end
