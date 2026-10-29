from pathlib import Path
L=Path('evidence/pv-b3p6-20261028/lean');files={}
h='''namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 PV_B3P_Binding11227 PV_B3P_Binding12227 PV_B3P_Binding13227 Result
set_option autoImplicit false
'''
files['PV_B3P_NativePreweighted15227']='import PV_B3P_PreweightedMacro12227\nimport PV_B3P_Operations12227\n'+h+'''
/-- The source macro executes all four lane slots before the packed read,
pack call, addition and write. Empty and invalid spans keep their Result. -/
def native_preweighted15 {N : Usize} (packed : Array aspis_core.field.QM31 24#usize)
    (start : Usize) (values : Array aspis_core.field.QM31 N) :
    Result (Array aspis_core.field.QM31 24#usize) := do
  let first ← start / 4#usize
  let stop ← lift (Usize.wrapping_add start N)
  let before ← lift (Usize.wrapping_sub stop 1#usize)
  let last ← before / 4#usize
  loop (inclusive_body12 (source_preweighted_macro_step12 start values) last) (packed,first)

theorem native_preweighted_binding15 : @native_preweighted15 = @reference_terminal.add_preweighted := by
  have steps : ∀ (N : Usize) (start : Usize) (values : Array aspis_core.field.QM31 N),
      source_preweighted_macro_step12 start values = preweighted_source_step12 start values := by
    intro N start values
    funext packed group
    exact preweighted_macro_step_binding12 start values packed group
  funext N packed start values
  unfold native_preweighted15
  rw [steps]
  exact (congrFun (congrFun (congrFun (congrFun preweighted_operation_binding12 N) packed) start) values).symm
#print axioms native_preweighted_binding15
end PV_B3P_Native15227
'''
files['PV_B3P_NativeDigestStore15227']='import PV_B3P_NativeLeading15227\n'+h+'''
def native_digest_store15 (output : Array aspis_core.field.QM31 8#usize)
    (selector : aspis_core.field.QM31) (opened : Array aspis_core.field.QM31 16#usize)
    (start : Usize) (expected : Array aspis_core.field.M31 8#usize) (right_tweak : Bool) :
    Result (Array aspis_core.field.QM31 8#usize) :=
  range_loop13 (digest_store_cell11 selector opened start expected right_tweak) 0#usize 8#usize output

theorem native_digest_store_binding15 (output : Array aspis_core.field.QM31 8#usize)
    (selector : aspis_core.field.QM31) (opened : Array aspis_core.field.QM31 16#usize)
    (start : Usize) (expected : Array aspis_core.field.M31 8#usize) (right_tweak : Bool) :
    native_digest_store15 output selector opened start expected right_tweak =
      reference_terminal.add_digest_binding output selector opened start expected right_tweak := by
  unfold native_digest_store15
  rw [range_as_fold13 _ 0#usize 8#usize 8 _ (by rfl),leading_indices15]
  exact (digest_store_fold11 output selector opened start expected right_tweak).symm
#print axioms native_digest_store_binding15
end PV_B3P_Native15227
'''
files['PV_B3P_NativeActive15227']='import PV_B3P_CopyActiveLoop12227\n'+h+'''
def native_active15 (selectors : reference_copy_terminal.Selectors) : Result aspis_core.field.QM31 :=
  loop (usize_body (active_step12 selectors) 64#usize) (aspis_core.field.QM31.ZERO,0#usize)

theorem native_active_binding15 (selectors : reference_copy_terminal.Selectors) :
    native_active15 selectors = reference_copy_terminal.Selectors.active_literal selectors := by
  change _ = reference_copy_terminal.Selectors.active_literal_loop selectors _ _
  exact (active_loop_binding12 selectors _ _).symm
#print axioms native_active_binding15
end PV_B3P_Native15227
'''
files['PV_B3P_NativeSharedRead15227']='import PV_B3P_ReconstructNative14227\nimport PV_B3P_EqualityNative14227\n'+h+'''
open PV_B3P_Loans14227
/-- Copying a shared array argument for a value read preserves its loan token.
The exact extracted read helper is only an indexed immutable read. -/
def shared_read15 {N : Usize} (loan : Shared14 (Array aspis_core.field.QM31 N)) (index : Usize) :=
  reference_terminal.read227 loan.value index

theorem shared_read_binding15 {N : Usize}
    (loan : Shared14 (Array aspis_core.field.QM31 N)) (index : Usize) :
    shared_read15 loan index = Array.index_usize loan.value index := rfl

theorem shared_read_success15 {N : Usize}
    (loan : Shared14 (Array aspis_core.field.QM31 N)) (index : Usize) (bound : index.val < N.val) :
    ∃ value, shared_read15 loan index = .ok value := by
  rw [shared_read_binding15]
  exact ⟨_,PV_B3P_SelectIndex227.index_value loan.value index bound⟩

theorem shared_read_preserves_identity15 {N : Usize}
    (loan : Shared14 (Array aspis_core.field.QM31 N)) (index : Usize) :
    (do let value ← shared_read15 loan index; .ok (loan.identity,value)) =
      (do let value ← Array.index_usize loan.value index; .ok (loan.identity,value)) := by
  rw [shared_read_binding15]
#print axioms shared_read_binding15
#print axioms shared_read_success15
#print axioms shared_read_preserves_identity15
end PV_B3P_Native15227
'''
# Repair only the arithmetic shape of the rejected prior module. Avoid concretizing UScalar.size.
files['PV_B3P_NativeMaskSafety15227']='import PV_B3P_MaskIndexNative14227\n'+h+'''
open PV_B3P_Correct14227 PV_B3P_Success227

theorem native_mask_subtraction_safe15 (mask : U16) (nonzero : mask ≠ 0#u16) :
    1 ≤ mask.val ∧ mask.val-1 < UScalar.size .U16 := by
  have positive : 0 < mask.val := by scalar_tac
  have bound : mask.val < UScalar.size .U16 := by
    simpa only [UScalar.size] using mask.hBounds
  omega

theorem native_mask_read_success15 (values : Array aspis_core.field.QM31 16#usize)
    (mask : U16) (allowed : MaskAllowed mask) (index : Nat)
    (member : index ∈ PV_B3P_Mask227.walk 16 mask.val) :
    ∃ value, mask_read10 values index = .ok value := by
  have bound := mask_walk_indices14 mask allowed index member
  rw [mask_read_source_index14 values index bound]
  exact ⟨_,PV_B3P_SelectIndex227.index_value values (mask_index14 index bound) bound⟩
#print axioms native_mask_subtraction_safe15
#print axioms native_mask_read_success15
end PV_B3P_Native15227
'''
for m,s in files.items():
 s='import PV_B3P_Operations12227\nimport PV_B3P_RangeFold13227\n'+s
 (L/(m+'.lean')).write_text(s)
print(' '.join(files))
