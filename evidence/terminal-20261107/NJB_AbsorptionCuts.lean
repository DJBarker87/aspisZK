import NJB_AbsorptionAssociation
import NJB_PreparedCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJB_AbsorptionCuts
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIv_PreparedNew (NP)
/-- Exact K046 lane assertions on the ACTUAL nine-word prepared carrier. It
contains neither a multiplication equation nor an output-success premise. -/
def lane (scales : Fin 3 → NP) (opened : Fin 16 → NQ) (i : Fin 16)
 (reply out : NQ) (cacheSeen : NP) (right : NQ) (kind calls : Nat) : Prop :=
 calls=1 ∧ kind=3 ∧ cacheSeen=scales (NJB_AbsorptionLane.group i) ∧ right=opened i ∧ out=reply
/-- Same-call prepared domain is constructed by the root's scale laws. This
support lemma discharges the complete child Result at the selected cache. -/
theorem discharge (scales : Fin 3 → NJB_AbsorptionScales.Scale) (opened : Fin 16 → NQ) (i : Fin 16)
 (prepared : ∀ j,Canon (scales j).value ∧ NJB_PreparedLaws.Domain (scales j).cache (scales j).value)
 (canonical : ∀ j,Canon (opened j)) :
 ∃ reply,FIq_Native.field.PreparedQm31Multiplier.mul (scales (NJB_AbsorptionLane.group i)).cache (opened i)=ok reply ∧
 Canon reply ∧ ∀ out seen right kind calls,
 lane (fun j=>(scales j).cache) opened i reply out seen right kind calls →
 FIq_Native.field.PreparedQm31Multiplier.mul (scales (NJB_AbsorptionLane.group i)).cache (opened i)=ok out := by
 obtain ⟨reply,call,hr,_⟩ := NJB_AbsorptionLane.result scales opened i prepared canonical
 refine ⟨reply,call,hr,?_⟩
 intro out seen right kind calls cut
 rw [cut.2.2.2.2]
 exact call
#print discharge
#print axioms discharge
end AspisR1.NJB_AbsorptionCuts
end
