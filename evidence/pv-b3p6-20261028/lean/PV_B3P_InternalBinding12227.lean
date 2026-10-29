import PV_B3P_InternalSum1201227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 Result
set_option autoImplicit false

def source_internal12 (state : InternalState12) : Result InternalState12 := do
  let first ← Array.index_usize state 0#usize
  let old_zero ← reference_poseidon.extension_limbs first
  let initial := Array.repeat 4#usize 0#u64
  let part_sum ← PV_B3P_Ordered227.fold (internal_sum_step12 state)
    [1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize,8#usize,
     9#usize,10#usize,11#usize,12#usize,13#usize,14#usize,15#usize] initial
  internal_finish12 state old_zero part_sum

attribute [local irreducible] Array.index_usize Array.update
  reference_poseidon.extension_limbs reference_poseidon.internal_sum227
  reference_poseidon.internal_full_sum227 reference_poseidon.internal_zero227
  reference_poseidon.internal_shift227

theorem internal_linear_binding12 (state : InternalState12) :
    reference_poseidon.internal_linear_lazy state = source_internal12 state := by
  unfold reference_poseidon.internal_linear_lazy source_internal12
  apply bind_equal9
  intro first
  apply bind_equal9
  intro old_zero
  exact internal_sum_fold12_01 state old_zero (Array.repeat 4#usize 0#u64)

#print axioms internal_linear_binding12
end PV_B3P_Binding12227
