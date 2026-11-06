import NKR_TermPublic
import NLH_TermSelected
import NLH_TermPartsFactor
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_TermWrapperFactor
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open pool_v1.pair_forest_semantic_terminal
abbrev Public := r0.Public
abbrev Challenges := state_only_prefix.r0.Challenges
abbrev Error := state_only_prefix.r0.Error

def after : core.result.Result NKR_TermTail.Output NKR_TermTail.Error → Result (core.result.Result NQ Error)
 | .Ok parts=>ok (.Ok parts.1)
 | .Err _=>ok (.Err .Public)

def reference (pub : Public) (selected : Array NQ 84#usize) (point : Array NQ 10#usize) (c : Challenges) := do
 let parts←terminal_parts (NKR_TermPublic.value pub) selected point c.lambda c.chi c.theta c.zc c.mu
 after parts

/--256 complete emitted prefix and full map/map_err association. CLOSED255
is internally instantiated on the exact pub; the84cell gather is built from
actual3x29claims.263 remains inside the reference at SAME actual arguments.
This is support until263 and the native parent windows compose. -/
theorem source (pub : Public) (claims : NLH_TermSelected.Claims)
 (point : Array NQ 10#usize) (c : Challenges)
 (hc : ∀ row∈claims.val,FIw_ArrayValue.canonical row) :
 ∃ selected,
 array_from_fn_copy 84#usize field.QM31.Insts.CoreMarkerCopy NLH_TermSelected.builder field.QM31.ZERO claims=ok selected ∧
 FIw_ArrayValue.canonical selected ∧
 r0.Public.terminal_qm31 pub claims point c=reference pub selected point c := by
 obtain ⟨selected,call,canonical,_⟩:=NLH_TermSelected.source claims hc
 refine ⟨selected,call,canonical,?_⟩
 unfold r0.Public.terminal_qm31 reference
 rw [call,bind_tc_ok,NKR_TermPublic.source,bind_tc_ok]
 cases actual : terminal_parts (NKR_TermPublic.value pub) selected point c.lambda c.chi c.theta c.zc c.mu with
 | fail e=>rfl
 | div=>rfl
 | ok r=>cases r <;> rfl
#print source
#print axioms source
end AspisR1.NLH_TermWrapperFactor
end
