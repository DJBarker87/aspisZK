from pathlib import Path
L=Path('evidence/pv-b3p6-20261028/lean');h='''namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 PV_B3P_Binding11227 PV_B3P_Binding12227 PV_B3P_Binding13227 Result
set_option autoImplicit false
'''
s='import PV_B3P_Operations12227\nimport PV_B3P_InternalBinding12227\nimport PV_B3P_RangeFold13227\n'+h+'''
theorem internal_indices15 : usize_indices11 15 1#usize =
    [1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize,8#usize,
      9#usize,10#usize,11#usize,12#usize,13#usize,14#usize,15#usize] := by
  simp only [usize_indices11,next11_20_1,next11_20_2,next11_20_3,next11_20_4,
    next11_20_5,next11_20_6,next11_20_7,next11_20_8,next11_20_9,next11_20_10,
    next11_20_11,next11_20_12,next11_20_13,next11_20_14,next11_20_15]

def native_internal_sum15 (state : InternalState12) (sum : InternalSum12) : Result InternalSum12 :=
  loop (usize_body (internal_sum_step12 state) 16#usize) (sum,1#usize)

theorem native_internal_sum_binding15 (state : InternalState12) (sum : InternalSum12) :
    native_internal_sum15 state sum = internal_sum_sequence12 state sum := by
  unfold native_internal_sum15
  rw [loop_as_fold11 _ 16#usize 1#usize 15 sum (by rfl),internal_indices15]
  exact (internal_sum_sequence_fold12 state sum).symm
#print axioms internal_indices15
#print axioms native_internal_sum_binding15
end PV_B3P_Native15227
''';(L/'PV_B3P_NativeInternalSum15227.lean').write_text(s)
s='import PV_B3P_NativeInternalSum15227\n'+h+'''
def native_internal_finish15 (state : InternalState12) (old_zero : Array U32 4#usize)
    (part_sum : InternalSum12) : Result InternalState12 := do
  let full_sum ← reference_poseidon.internal_full_sum227 part_sum old_zero
  let first ← reference_poseidon.internal_zero227 part_sum old_zero
  let state1 ← Array.update state 0#usize first
  range_loop13 (internal_output_step12 full_sum) 1#usize 16#usize state1

theorem native_internal_finish_binding15 (state : InternalState12)
    (old_zero : Array U32 4#usize) (part_sum : InternalSum12) :
    native_internal_finish15 state old_zero part_sum = internal_finish12 state old_zero part_sum := by
  unfold native_internal_finish15 internal_finish12
  apply bind_equal9
  intro full_sum
  apply bind_equal9
  intro first
  apply bind_equal9
  intro state1
  rw [range_as_fold13 _ 1#usize 16#usize 15 state1 (by rfl),internal_indices15]
  exact (internal_output_fold12_01 full_sum state1).symm
#print axioms native_internal_finish_binding15
end PV_B3P_Native15227
''';(L/'PV_B3P_NativeInternalFinish15227.lean').write_text(s)
s='import PV_B3P_NativeInternalFinish15227\n'+h+'''
def native_internal15 (state : InternalState12) : Result InternalState12 := do
  let first ← Array.index_usize state 0#usize
  let old_zero ← reference_poseidon.extension_limbs first
  let part_sum ← native_internal_sum15 state (Array.repeat 4#usize 0#u64)
  native_internal_finish15 state old_zero part_sum

theorem native_internal_binding15 (state : InternalState12) :
    native_internal15 state = reference_poseidon.internal_linear_lazy state := by
  rw [internal_entry_factor12]
  unfold native_internal15 internal_entry_prefix12
  simp only [native_internal_sum_binding15,native_internal_finish_binding15]
#print axioms native_internal_binding15
end PV_B3P_Native15227
''';(L/'PV_B3P_NativeInternal15227.lean').write_text(s)
