import NLU_CanonicalTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Terminal
open Aeneas Aeneas.Std Result AspisR1PublicPreparation FIq_Carriers
theorem canonical_from_native (q : FIv_NativeArithmetic.NQ) (h : FIv_NativeValue.Canon q) :
 JFv_RoundArithmetic.Canonical (fromQ q) := by exact h
def Outcome : Result (core.result.Result aspis_core.field.QM31 FIq_Terminal.Error) → Prop
 | .ok (.Ok value)=>JFv_RoundArithmetic.Canonical value
 | _=>True
def convert (out : NLH_WrapperRoot.Outcome) : Result (core.result.Result aspis_core.field.QM31 FIq_Terminal.Error) := do
 let result ← NLH_WrapperRoot.projected out
 match result with
 | .Ok q=>ok (.Ok (fromQ q))
 | .Err e=>ok (.Err (FIq_Terminal.fromError e))
theorem converted (out : NLH_WrapperRoot.Outcome) (canonical : NLH_WrapperRoot.Canonical out) :
 Outcome (convert out) := by
 cases out with
 | fail err=>trivial
 | div=>trivial
 | ok result=>cases result with
   | Err err=>trivial
   | Ok state=>exact canonical_from_native _ canonical
/-- SAME256 returned value supplies the parent's multiplication domain on
its successful branch. Err and abort stay complete alternatives. -/
theorem source (r : NP6_StdModel.Reservation) (pub : Public) (claims : NLC_Finish.Claims)
 (alpha : NLC_Finish.Alpha) (c : r1_wire.Challenges) (domain : InputDomain pub c)
 (hc : ∀ row∈(mapArray (mapArray toQ) claims).val,FIw_ArrayValue.canonical row)
 (ha : FIw_ArrayValue.canonical (mapArray toQ alpha)) :
 Outcome ((IDa_Deployed.boundaries r).terminal pub claims alpha c) := by
 obtain ⟨result,events,cuts,attempted,canonical,projected,reference⟩:=install pub claims alpha c domain hc ha
 have same : convert result=FIq_Terminal.terminal pub claims alpha c := by
  unfold convert FIq_Terminal.terminal
  rw [projected]
  rfl
 rw [←same]
 exact converted result canonical
#print axioms canonical_from_native
#print axioms converted
#print axioms source
end AspisR1.NLU_Terminal
end
