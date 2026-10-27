import RPv_FJh_Base
import RPv_FJh_Base

/-! Read/model/bound facts for the actual fifteen shift entries. These
literal U8 checks do not evaluate a field or internal-round computation. -/
set_option autoImplicit false
namespace AspisR1.FJh_InternalShiftsExact
open Aeneas Aeneas.Std Result
open FIq_Native
open AspisR1.FJh_Base (cell)

def shift (r : Fin 15) : U8 := cell state_only_poseidon.internal_linear_lazy.SHIFTS r

theorem source_read (r : Usize) (hr : r.val < 15) :
    Array.index_usize state_only_poseidon.internal_linear_lazy.SHIFTS r = .ok (shift ⟨r.val,hr⟩) := by
  have hb : r.val < (15#usize).val := by simpa using hr
  simpa only [shift,cell] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok
    state_only_poseidon.internal_linear_lazy.SHIFTS r hb

theorem model (r : Fin 15) : (shift r).val = R0P.poseidonInternalShifts r := by
  unfold shift cell state_only_poseidon.internal_linear_lazy.SHIFTS R0P.poseidonInternalShifts
  fin_cases r <;> rfl

theorem bounded (r : Fin 15) : (shift r).val ≤ 16 := by
  unfold shift cell state_only_poseidon.internal_linear_lazy.SHIFTS
  fin_cases r <;> decide

#print axioms source_read
#print axioms model
#print axioms bounded
end AspisR1.FJh_InternalShiftsExact
