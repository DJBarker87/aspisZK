import Lean
import NGU_Part005
import NGU_Part007
-- Retargeted LPt_ByteDomain
set_option autoImplicit false
namespace AspisR1.NGU_LPt_ByteDomain
open Aeneas Aeneas.Std Result

/-- The two producer predicates are converted in this same environment, on the
same input and output bytes. No decoder-success premise is supplied. -/
theorem natural (compact before y1 : Slice U8)
    (len : compact.val.length=464) (size : before.val.length=928)
    (checked : NFU_Retarget.compact.check_values compact=ok (.Ok ()))
    (trace : NFU_Retarget.LPn.Expand.NativeTrace compact.val before.val 29 y1.val) :
    y1.val.length=928 ∧ NGU_LPq_ExpandedWords.Expanded compact.val y1.val ∧
      NGU_LPq_ExpandedWords.CompactCanonical compact.val := by
  obtain ⟨length,expanded,_⟩ := NGU_LPt_LPs_ExpandDomain.expanded compact before y1 len size trace
  exact ⟨length,expanded,NGU_LPt_LPs_CheckDomain.checked compact len checked⟩

theorem checked_expanded (compact before y1 : Slice U8)
    (len : compact.val.length=464) (size : before.val.length=928)
    (checked : NFU_Retarget.compact.check_values compact=ok (.Ok ()))
    (trace : NFU_Retarget.LPn.Expand.NativeTrace compact.val before.val 29 y1.val) :
    NGU_LPq_SelectedDomain.ByteDomain y1 := by
  obtain ⟨length,expanded,canonical⟩ := natural compact before y1 len size checked trace
  exact NGU_LPs_NaturalDomain.selected compact y1 length expanded canonical

#print axioms natural
#print axioms checked_expanded
end AspisR1.NGU_LPt_ByteDomain

-- Retargeted LPt_LPs_ProducerTotal
set_option autoImplicit false
namespace AspisR1.NGU_LPt_LPs_ProducerTotal
open Aeneas Aeneas.Std Result

/-- Every caller-shaped compact/initial pair has an expansion trace and the
exact native expansion result. Its byte output is constructed, never assumed.
The check success remains an actual input observation for checked callers. -/
theorem expansion (compact initial : Slice U8)
    (len : compact.val.length=464) (size : initial.val.length=928) :
    ∃ y1 : Slice U8, NFU_Retarget.LPn.Expand.NativeTrace compact.val initial.val 29 y1.val ∧
      y1.val.length=928 ∧ NGU_LPt_LPs_ExpandDomain.Expanded compact.val y1.val ∧
      _root_.NFU_Retarget.compact.expand_values compact initial=ok (.Ok (),y1) := by
  obtain ⟨after,trace⟩ := NFU_Retarget.LPn.Expand.total compact.val initial.val 29
  have length := NFU_Retarget.LPl.Expand.length _ _ _ _ (NFU_Retarget.LPn.Expand.to_inherited _ _ _ _ trace)
  let y1 : Slice U8 := ⟨after,by rw [length];exact initial.property⟩
  exact ⟨y1,trace,NGU_LPt_LPs_ExpandDomain.expanded compact initial y1 len size trace⟩

#print axioms expansion
end AspisR1.NGU_LPt_LPs_ProducerTotal

-- Retargeted LPt_PreparedClaim
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGU_LPt_PreparedClaim
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisR1ClaimPreparedBridge
open NFN_LPi_FieldValues

/-- Same-carrier prepared_claim join. The natural compact/expanded predicates,
semantic canonicality and powers canonicality are all derived from producers. -/
theorem native_result (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
    (beforeSemantic : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (obs : Option (verifier.Phase → Result Unit)) (sem : r1_semantic.Verified H)
    (finish : FinishModel.finish AspisS1ExtractedRoundChildren.children {B with claims:=ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ()))}
      D pub pre beforeSemantic challenges obs=ok (.Ok sem))
    (compact before y1 : Slice U8) (len : compact.val.length=464)
    (size : before.val.length=928)
    (checked : NFU_Retarget.compact.check_values compact=ok (.Ok ()))
    (trace : NFU_Retarget.LPn.Expand.NativeTrace compact.val before.val 29 y1.val)
    (gamma inactive kappa : NE) (hc : canonE gamma) (hi : canonE inactive) (hk : canonE kappa)
    (g : Array NE 29#usize) (powers : FIo_Native.weights.powers 29#usize gamma=ok g) :
    ∃ out, NGU_LPq_PreparedTrace.Trace (toClaimSem sem) y1 (NGU_Carriers.arr NGU_Powers.claim g)
        inactive kappa out ∧ canonE out ∧
      NGU_LPq_PreparedClaim.program (toClaimSem sem) y1 (NGU_Carriers.arr NGU_Powers.claim g)
        inactive kappa=fun _ => ok (.Ok (NGU_Powers.claim out)) := by
  obtain ⟨length,expanded,canonical⟩ :=
    NGU_LPt_ByteDomain.natural compact before y1 len size checked trace
  exact NGU_LPs_PreparedClaim.native_result B D pub pre beforeSemantic challenges obs sem finish
    compact y1 length expanded canonical gamma inactive kappa hc hi hk g powers

/-- Construct the expansion/output on every caller-shaped initial buffer.
Neither the output bytes nor prepared result are supplied as hypotheses. -/
theorem construct (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
    (beforeSemantic : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (obs : Option (verifier.Phase → Result Unit)) (sem : r1_semantic.Verified H)
    (finish : FinishModel.finish AspisS1ExtractedRoundChildren.children {B with claims:=ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ()))}
      D pub pre beforeSemantic challenges obs=ok (.Ok sem))
    (compact before : Slice U8) (len : compact.val.length=464)
    (size : before.val.length=928)
    (checked : NFU_Retarget.compact.check_values compact=ok (.Ok ()))
    (gamma inactive kappa : NE) (hc : canonE gamma) (hi : canonE inactive) (hk : canonE kappa)
    (g : Array NE 29#usize) (powers : FIo_Native.weights.powers 29#usize gamma=ok g) :
    ∃ y1 : Slice U8, NFU_Retarget.LPn.Expand.NativeTrace compact.val before.val 29 y1.val ∧
      NFU_Retarget.compact.expand_values compact before=ok (.Ok (),y1) ∧
      ∃ out, NGU_LPq_PreparedTrace.Trace (toClaimSem sem) y1 (NGU_Carriers.arr NGU_Powers.claim g)
        inactive kappa out ∧ canonE out ∧
      NGU_LPq_PreparedClaim.program (toClaimSem sem) y1 (NGU_Carriers.arr NGU_Powers.claim g)
        inactive kappa=fun _ => ok (.Ok (NGU_Powers.claim out)) := by
  obtain ⟨y1,trace,_,_,expanded⟩ := NGU_LPt_LPs_ProducerTotal.expansion compact before len size
  exact ⟨y1,trace,expanded,native_result B D pub pre beforeSemantic challenges obs sem finish
    compact before y1 len size checked trace gamma inactive kappa hc hi hk g powers⟩

#print axioms construct

#print axioms native_result
#print axioms NGU_LPq_CarrierFacts.native_unique
end AspisR1.NGU_LPt_PreparedClaim
end

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
