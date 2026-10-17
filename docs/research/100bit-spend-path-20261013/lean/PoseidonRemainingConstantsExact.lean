import PoseidonRemainingConstantSource
import PoseidonInitialConstantsExact

/-! Exact final full-round rows and internal constants: only literal table
reads/bounds are reduced. The round computations remain opaque. -/
set_option autoImplicit false
namespace AspisR1.PoseidonRemainingConstantsExact
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep

def finalRow (r : Fin 4) : Constants := cell poseidon2.EXTERNAL_FINAL r

theorem final_source_read (r : Usize) (hr : r.val < 4) :
    Array.index_usize poseidon2.EXTERNAL_FINAL r = .ok (finalRow ⟨r.val,hr⟩) := by
  have hb : r.val < (4#usize).val := by simpa using hr
  simpa only [finalRow,cell] using
    AspisR1.ExtractedMaskHornerStep.array_index_usize_ok poseidon2.EXTERNAL_FINAL r hb

theorem final_canonical (r : Fin 4) : CanonicalConstants (finalRow r) := by
  intro lane
  unfold finalRow cell poseidon2.EXTERNAL_FINAL
  fin_cases r <;> fin_cases lane <;> decide

theorem final_model {K : Type} [Field K] (r : Fin 4) (lane : Fin 16) :
    ((cell (finalRow r) lane).val : K) = R0P.poseidonExternalFinal (K := K) r lane := by
  unfold finalRow cell poseidon2.EXTERNAL_FINAL R0P.poseidonExternalFinal
  fin_cases r <;> fin_cases lane <;> rfl

def internalConstant (r : Fin 14) : U32 := cell poseidon2.INTERNAL r

theorem internal_source_read (r : Usize) (hr : r.val < 14) :
    Array.index_usize poseidon2.INTERNAL r = .ok (internalConstant ⟨r.val,hr⟩) := by
  have hb : r.val < (14#usize).val := by simpa using hr
  simpa only [internalConstant,cell] using
    AspisR1.ExtractedMaskHornerStep.array_index_usize_ok poseidon2.INTERNAL r hb

theorem internal_canonical (r : Fin 14) : (internalConstant r).val < P := by
  unfold internalConstant cell poseidon2.INTERNAL
  fin_cases r <;> decide

theorem internal_model {K : Type} [Field K] (r : Fin 14) :
    ((internalConstant r).val : K) = R0P.poseidonInternalConstants (K := K) r := by
  unfold internalConstant cell poseidon2.INTERNAL R0P.poseidonInternalConstants
  fin_cases r <;> rfl

#print axioms final_source_read
#print axioms final_canonical
#print axioms final_model
#print axioms internal_source_read
#print axioms internal_canonical
#print axioms internal_model
end AspisR1.PoseidonRemainingConstantsExact
