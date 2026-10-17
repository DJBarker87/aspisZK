import PoseidonInternalPairCallbacks
import PoseidonArrayMapStable
import PoseidonM31DotReads

/-! The three actual seven-row maps at the internal-pair caller. Source
callbacks are proved on exactly the rows present in the literal row table. -/
set_option autoImplicit false
namespace AspisR1.PoseidonInternalPairMaps
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep (State QM CanonicalState cell)
open AspisR1.PoseidonInternalPairCallbacks
open AspisR1.PoseidonArrayMapStable (mapped)

def row (i : Fin 7) : Usize := UScalar.ofNatCore (i.val+2) (by scalar_tac)
theorem row_value (i : Fin 7) : (row i).val = i.val+2 := rfl

theorem rows_model : state_only_poseidon.interpolated_internal_pair.ROWS.val = List.ofFn row := by
  unfold state_only_poseidon.interpolated_internal_pair.ROWS row
  rfl

theorem row_bounds (r : Usize) (hr : r ∈ state_only_poseidon.interpolated_internal_pair.ROWS.val) :
    2 ≤ r.val ∧ r.val ≤ 8 := by
  rw [rows_model] at hr
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hr
  subst r
  rw [row_value]
  have := i.isLt
  omega

def weights (local1 : State) : Array QM 7#usize :=
  mapped state_only_poseidon.interpolated_internal_pair.ROWS (weightValue local1)
def constants (parity : Nat) : Array U32 7#usize :=
  mapped state_only_poseidon.interpolated_internal_pair.ROWS (fun r => constantValue r parity)

theorem weights_source (local1 : State) :
    core.array.Array.map
      state_only_poseidon.interpolated_internal_pair.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      state_only_poseidon.interpolated_internal_pair.ROWS local1 = .ok (weights local1) := by
  apply AspisR1.PoseidonArrayMapStable.source_success
  intro r hr
  have hb := row_bounds r hr
  exact weight_source local1 r (by omega)

theorem even_source :
    core.array.Array.map
      state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31
      state_only_poseidon.interpolated_internal_pair.ROWS () = .ok (constants 0) := by
  apply AspisR1.PoseidonArrayMapStable.source_success
  intro r hr
  have hb := row_bounds r hr
  exact AspisR1.PoseidonInternalPairCallbacks.even_source r hb.1 hb.2

theorem odd_source :
    core.array.Array.map
      state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31
      state_only_poseidon.interpolated_internal_pair.ROWS () = .ok (constants 1) := by
  apply AspisR1.PoseidonArrayMapStable.source_success
  intro r hr
  have hb := row_bounds r hr
  exact AspisR1.PoseidonInternalPairCallbacks.odd_source r hb.1 hb.2

theorem weights_model (local1 : State) (i : Fin 7) :
    cell (weights local1) i = cell local1 ⟨i.val+2,by have := i.isLt; omega⟩ := by
  change ((state_only_poseidon.interpolated_internal_pair.ROWS.val.map (weightValue local1))[i.val]'_) = _
  rw [List.getElem_map,rows_model,List.getElem_ofFn]
  unfold weightValue
  apply congrArg (cell local1)
  apply Fin.ext
  rw [row_value,Nat.mod_eq_of_lt (by have := i.isLt; omega)]

theorem constants_model (parity : Nat) (hp : parity ≤ 1) (i : Fin 7) :
    cell (constants parity) i = AspisR1.PoseidonRemainingConstantsExact.internalConstant
      ⟨2*i.val+parity,by have := i.isLt; omega⟩ := by
  change ((state_only_poseidon.interpolated_internal_pair.ROWS.val.map (fun r => constantValue r parity))[i.val]'_) = _
  rw [List.getElem_map,rows_model,List.getElem_ofFn]
  unfold constantValue constantIndex
  apply congrArg AspisR1.PoseidonRemainingConstantsExact.internalConstant
  apply Fin.ext
  rw [row_value]
  have hsub : i.val+2-2=i.val := by omega
  rw [hsub,Nat.mod_eq_of_lt (by have := i.isLt; omega)]

theorem weights_canonical (local1 : State) (hc : CanonicalState local1) :
    AspisR1.PoseidonM31DotReads.CanonicalWeights (Array.to_slice (weights local1)) := by
  intro i hi
  change AspisR1.PoseidonFullRoundCellStep.Canonical
    ((state_only_poseidon.interpolated_internal_pair.ROWS.val.map (weightValue local1))[i]'hi)
  rw [List.getElem_map]
  exact hc _

theorem constants_canonical (parity : Nat) :
    AspisR1.PoseidonM31DotReads.CanonicalValues (Array.to_slice (constants parity)) := by
  intro i hi
  change ((state_only_poseidon.interpolated_internal_pair.ROWS.val.map (fun r => constantValue r parity))[i]'hi).val < _
  rw [List.getElem_map]
  exact AspisR1.PoseidonRemainingConstantsExact.internal_canonical _

#print axioms rows_model
#print axioms weights_source
#print axioms even_source
#print axioms odd_source
#print axioms weights_model
#print axioms constants_model
#print axioms weights_canonical
#print axioms constants_canonical
end AspisR1.PoseidonInternalPairMaps
