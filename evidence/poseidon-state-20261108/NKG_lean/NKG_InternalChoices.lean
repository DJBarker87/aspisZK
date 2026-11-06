import NKG_InternalSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_InternalChoices
open Aeneas Aeneas.Std Result FIq_Native
open FJh_Base (State QM)
def get {A : Type} (r : Result A) (fallback : A) : A :=
 match r with | .ok x => x | _ => fallback
/-- Only an eliminator for the complete Result. Fallbacks are proved
unreachable on caller domains, not asserted away. -/
theorem get_ok {A : Type} (r : Result A) (fallback x : A) (run : r=ok x) :
 get r fallback=x := by rw [run];rfl

def weights (l : State) := get (FIq_Native.core.array.Array.map FJh_InternalWeights.callback FJh_InternalWeights.rows l)
 (Array.repeat 7#usize field.QM31.ZERO)
def evens := get (FIq_Native.core.array.Array.map FJh_InternalConstantCalls.even FJh_InternalWeights.rows ())
 (Array.repeat 7#usize 0#u32)
def odds := get (FIq_Native.core.array.Array.map FJh_InternalConstantCalls.odd FJh_InternalWeights.rows ())
 (Array.repeat 7#usize 0#u32)
def even (l : State) := get (field.qm31_m31_dot (Array.to_slice (weights l)) (Array.to_slice evens)) field.QM31.ZERO
def odd (l : State) := get (field.qm31_m31_dot (Array.to_slice (weights l)) (Array.to_slice odds)) field.QM31.ZERO
def middle (s l : State) := get (state_only_poseidon.internal_round s (even l)) (Array.repeat 16#usize field.QM31.ZERO)
def last (s l : State) := get (state_only_poseidon.internal_round (middle s l) (odd l)) (Array.repeat 16#usize field.QM31.ZERO)
/-- Resolve each chosen reply from THIS source invocation's ordered calls. -/
theorem value (s l out : State) (run : state_only_poseidon.interpolated_internal_pair s l=ok out) :
 last s l=out := by
 obtain ⟨w,e,o,ev,od,mid,rw,re,ro,rev,rod,rm,rf⟩ := FJh_InternalPairOrigins.reached s l out run
 have ww : weights l=w := get_ok _ _ _ rw
 have ee : evens=e := get_ok _ _ _ re
 have oo : odds=o := get_ok _ _ _ ro
 have ve : even l=ev := by unfold even;rw [ww,ee];exact get_ok _ _ _ rev
 have vo : odd l=od := by unfold odd;rw [ww,oo];exact get_ok _ _ _ rod
 have vm : middle s l=mid := by unfold middle;rw [ve];exact get_ok _ _ _ rm
 unfold last
 rw [vm,vo]
 exact get_ok _ _ _ rf
#print get_ok
#print axioms get_ok
#print value
#print axioms value
end AspisR1.NKG_InternalChoices
end
