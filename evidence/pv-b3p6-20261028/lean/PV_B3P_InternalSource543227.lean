import PV_B3P_ArrayInterface543227
import PV_B3P_NativeInternal15227
import PV_B3P_InternalLimb12227
import PV_B3P_InternalShift12227
import PV_B3P_InternalLink13227
namespace PV_B3P_Association543227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding12227 PV_B3P_Native15227 Result
set_option autoImplicit false

/-- The actual inner four-limb while loop, rather than a chosen reference
helper, is used at every source lane. All arithmetic remains wrapping. -/
def source_internal_sum_step543 (state : InternalState12) (sum : InternalSum12)
    (lane : Usize) : Result InternalSum12 := do
  let value ← Array.index_usize state lane
  source_internal_sum12 sum value

theorem internal_sum_step_binding543 (state : InternalState12) (sum : InternalSum12)
    (lane : Usize) :
    source_internal_sum_step543 state sum lane = internal_sum_step12 state sum lane := by
  unfold source_internal_sum_step543 internal_sum_step12
  apply congrArg (Aeneas.Std.bind (Array.index_usize state lane))
  funext value
  exact (internal_sum_helper_binding12 sum value).symm

def source_internal_sum543 (state : InternalState12) (sum : InternalSum12) : Result InternalSum12 :=
  loop (usize_body (source_internal_sum_step543 state) 16#usize) (sum,1#usize)

theorem internal_sum_binding543 (state : InternalState12) (sum : InternalSum12) :
    source_internal_sum543 state sum = native_internal_sum15 state sum := by
  have step : source_internal_sum_step543 state = internal_sum_step12 state :=
    funext fun acc => funext fun lane => internal_sum_step_binding543 state acc lane
  unfold source_internal_sum543 native_internal_sum15
  rw [step]

/-- Source state0 and all fifteen output state writes occur in native finish;
its from_fn callbacks are bound separately, including release wrap boundaries. -/
def source_internal543 (state : InternalState12) : Result InternalState12 := do
  let first ← Array.index_usize state 0#usize
  let old_zero ← reference_poseidon.extension_limbs first
  let part_sum ← source_internal_sum543 state (Array.repeat 4#usize 0#u64)
  native_internal_finish15 state old_zero part_sum

theorem internal_source_reference543 (state : InternalState12) :
    source_internal543 state = reference_poseidon.internal_linear_lazy state := by
  rw [← native_internal_binding15]
  unfold source_internal543 native_internal15
  simp only [internal_sum_binding543]

theorem internal_source_link543 :
    PV_B3P_Links13227.PV_B3P_Link_poseidon_internal_linear_lazy source_internal543 :=
  funext internal_source_reference543

#print axioms internal_sum_step_binding543
#print axioms internal_sum_binding543
#print axioms internal_source_reference543
#print axioms internal_source_link543
end PV_B3P_Association543227
