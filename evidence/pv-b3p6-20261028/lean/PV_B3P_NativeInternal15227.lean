import PV_B3P_NativeInternalFinish15227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 PV_B3P_Binding11227 PV_B3P_Binding12227 PV_B3P_Binding13227 Result
set_option autoImplicit false

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
