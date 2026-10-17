import PoseidonLeadingSourceDeclarationsV5
import AspisR1.PoseidonFullRoundCellStep
import ExtractedMaskHornerStep

/-! The fixed 4-by-16 initial table is small. These checks reduce only
literal U32 reads and bounds; no Poseidon round/permutation is evaluated. -/
set_option autoImplicit false
namespace AspisR1.PoseidonInitialConstantsExact
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep

def row (r : Fin 4) : Constants := cell poseidon2.EXTERNAL_INITIAL r

theorem row_source_read (r : Usize) (hr : r.val < 4) :
    Array.index_usize poseidon2.EXTERNAL_INITIAL r = .ok (row ⟨r.val,hr⟩) := by
  have hb : r.val < (4#usize).val := by simpa using hr
  simpa only [row,cell] using
    AspisR1.ExtractedMaskHornerStep.array_index_usize_ok poseidon2.EXTERNAL_INITIAL r hb

theorem row_canonical (r : Fin 4) : CanonicalConstants (row r) := by
  intro lane
  unfold row cell poseidon2.EXTERNAL_INITIAL
  fin_cases r <;> fin_cases lane <;> decide

theorem row_model {K : Type} [Field K] (r : Fin 4) (lane : Fin 16) :
    ((cell (row r) lane).val : K) = R0P.poseidonExternalInitial (K := K) r lane := by
  unfold row cell poseidon2.EXTERNAL_INITIAL R0P.poseidonExternalInitial
  fin_cases r <;> fin_cases lane <;> rfl

theorem source_read_canonical_model (r : Usize) (hr : r.val < 4) :
    ∃ constants1 : Constants,
      Array.index_usize poseidon2.EXTERNAL_INITIAL r = .ok constants1 ∧
      CanonicalConstants constants1 ∧ ∀ lane : Fin 16,
        ((cell constants1 lane).val : Exact) = R0P.poseidonExternalInitial ⟨r.val,hr⟩ lane := by
  exact ⟨row ⟨r.val,hr⟩,row_source_read r hr,row_canonical ⟨r.val,hr⟩,row_model ⟨r.val,hr⟩⟩

#print axioms row_source_read
#print axioms row_canonical
#print axioms row_model
#print axioms source_read_canonical_model
end AspisR1.PoseidonInitialConstantsExact
