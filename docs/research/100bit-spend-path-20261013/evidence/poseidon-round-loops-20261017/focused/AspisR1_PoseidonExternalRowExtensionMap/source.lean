import Aeneas
import RawPoseidonExtensionWords
import RawPoseidonExternalRowExact
import RawPoseidonRowField
import EmptyRootExecution

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1.PoseidonExternalRowExtensionMap
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisV8R19.TraversalRuntime

abbrev QM := field.QM31
abbrev Limbs := Array Std.U32 4#usize
abbrev Group := Array QM 4#usize
abbrev Input := AspisR1.RawPoseidonExternalRowWrapper.Input

def limbs (q : QM) : Limbs := Array.make 4#usize [q.c0.a, q.c0.b, q.c1.a, q.c1.b]

def groupInput (q0 q1 q2 q3 : QM) : Group := Array.make 4#usize [q0,q1,q2,q3]

def groupWords (q0 q1 q2 q3 : QM) : Input :=
  ⟨(groupInput q0 q1 q2 q3).val.map limbs, by
    simp [groupInput, Array.make, limbs]⟩

def groupCell (q0 q1 q2 q3 : QM) (i : Fin 4) : QM :=
  (groupInput q0 q1 q2 q3).val[i.val]'(by
    simpa [groupInput] using i.isLt)

theorem groupCell_eq (q0 q1 q2 q3 : QM) (i : Fin 4) :
    groupCell q0 q1 q2 q3 i =
      if i.val = 0 then q0 else if i.val = 1 then q1 else if i.val = 2 then q2 else q3 := by
  fin_cases i <;> rfl

theorem groupWords_decode (q0 q1 q2 q3 : QM) (i : Fin 4) :
    AspisR1.RawPoseidonRowField.decodeWords
      (fun j => AspisR1.RawPoseidonExternalRowExact.inputWords
        (groupWords q0 q1 q2 q3) i j) =
      AspisR1.ExtractedMaskQM31Exact.decode (groupCell q0 q1 q2 q3 i) := by
  fin_cases i <;>
    simp [AspisR1.RawPoseidonRowField.decodeWords,
      AspisR1.RawPoseidonExternalRowExact.inputWords,
      AspisR1.RawPoseidonExternalRowReads.rowValue,
      groupWords, groupCell, groupInput, limbs, Array.make,
      AspisR1.ExtractedMaskQM31Exact.decode]

theorem extension_map_state (qs : List QM) :
    mapState (BuiltinFnMut QM Limbs).call_mut qs state_only_poseidon.extension_limbs =
      .ok (qs.map limbs, state_only_poseidon.extension_limbs) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
      have hcall : ∀ x : QM,
          (BuiltinFnMut QM Limbs).call_mut state_only_poseidon.extension_limbs x =
            .ok (limbs x, state_only_poseidon.extension_limbs) := by
        intro x
        simp only [BuiltinFnMut, Function.comp_apply]
        rw [AspisR1.RawPoseidonExtensionWords.extension_limbs_words]
        rfl
      simp only [mapState, hcall, bind_tc_ok, List.map_cons, ih]

theorem group_extension_limbs_map (q0 q1 q2 q3 : QM) :
    core.array.Array.map (BuiltinFnMut QM Limbs)
      (groupInput q0 q1 q2 q3) state_only_poseidon.extension_limbs =
      .ok (groupWords q0 q1 q2 q3) := by
  have hstate := core.array.Array.map_success
    (BuiltinFnMut QM Limbs) (groupInput q0 q1 q2 q3)
    state_only_poseidon.extension_limbs
    ((groupInput q0 q1 q2 q3).val.map limbs)
    state_only_poseidon.extension_limbs
    (extension_map_state (groupInput q0 q1 q2 q3).val)
  simpa [groupWords] using hstate

/-- The generated row call on the four actual QM limbs returns the checked
row and its exact R0P matrix value. The row formula is expressed through the
actual extension-limb input consumed by the generated wrapper. -/
theorem group_row_success (q0 q1 q2 q3 : QM) (row : Usize)
    (hrow : row.val < 4) :
    ∃ out : QM,
      state_only_poseidon.external_linear_lazy_row
        (groupWords q0 q1 q2 q3) row = .ok out ∧
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM out ∧
      AspisR1.ExtractedMaskQM31Exact.decode out = R0P.poseidonMat4
        (fun i => AspisR1.ExtractedMaskQM31Exact.decode
          (groupCell q0 q1 q2 q3 i)) ⟨row.val, hrow⟩ := by
  obtain ⟨out, hrun, hcan, hmodel⟩ :=
    AspisR1.RawPoseidonExternalRowExact.external_linear_lazy_row_exact
      (groupWords q0 q1 q2 q3) row hrow
  refine ⟨out, hrun, hcan, ?_⟩
  simpa only [groupWords_decode] using hmodel

#print axioms extension_map_state
#print axioms group_extension_limbs_map
#print axioms group_row_success
end AspisR1.PoseidonExternalRowExtensionMap
