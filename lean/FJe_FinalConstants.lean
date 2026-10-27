import FJb_InitialConstants
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_FinalConstants
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (K)
open FJb_TailCell (cell)
def row (r : Fin 4) : FJb_M31Step.Constants := cell poseidon2.EXTERNAL_FINAL r
/-- Only fixed table reads,not a permutation or a recurrence. -/
theorem read (r : Usize) (hr : r.val < 4) :
    Array.index_usize poseidon2.EXTERNAL_FINAL r=ok (row ⟨r.val,hr⟩) := by
  exact RawPoseidonExternalRowReads.array_index_usize_ok poseidon2.EXTERNAL_FINAL r hr

theorem bounded (r : Fin 4) : FJb_M31Step.Bounded (row r) := by
  intro i
  unfold row cell poseidon2.EXTERNAL_FINAL
  fin_cases r <;> fin_cases i <;>
    norm_num [Array.make,FJb_M31Scalar.P,ExtractedMaskM31AddSub.P]

theorem model (r : Fin 4) (i : Fin (16#usize).val) :
    ((cell (row r) i).val : K)=R0P.poseidonExternalFinal r i := by
  unfold row cell poseidon2.EXTERNAL_FINAL R0P.poseidonExternalFinal
  fin_cases r <;> fin_cases i <;> rfl
#print axioms read
#print axioms bounded
#print axioms model
end AspisR1.FJe_FinalConstants
end
