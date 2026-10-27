import RPu_FJb_M31Step
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_InitialConstants
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (K)
open FJb_TailCell (cell)
/-- The actual fixed4x16 table. Only literal U32 reads and bounds are reduced;
no round,permutation or recurrence is evaluated. -/
def row (r : Fin 4) : FJb_M31Step.Constants := cell poseidon2.EXTERNAL_INITIAL r

theorem read (r : Usize) (hr : r.val < 4) :
    Array.index_usize poseidon2.EXTERNAL_INITIAL r=ok (row ⟨r.val,hr⟩) := by
  exact RawPoseidonExternalRowReads.array_index_usize_ok poseidon2.EXTERNAL_INITIAL r hr

theorem bounded (r : Fin 4) : FJb_M31Step.Bounded (row r) := by
  intro i
  unfold row cell poseidon2.EXTERNAL_INITIAL
  fin_cases r <;> fin_cases i <;>
    norm_num [Array.make,FJb_M31Scalar.P,ExtractedMaskM31AddSub.P]

theorem model (r : Fin 4) (i : Fin (16#usize).val) :
    ((cell (row r) i).val : K)=R0P.poseidonExternalInitial r i := by
  unfold row cell poseidon2.EXTERNAL_INITIAL R0P.poseidonExternalInitial
  fin_cases r <;> fin_cases i <;> rfl
#print axioms read
#print axioms bounded
#print axioms model
end AspisR1.FJb_InitialConstants
end
