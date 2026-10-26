import FIr_CarrierCanonical
import FIr_TerminalPartsValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_RootValue
open Aeneas Aeneas.Std Result
open FIq_Carriers
open FIr_NativeValue (Canon decode K)

theorem reached (pub : Public) (claims : Array (Array MQ 29#usize) 3#usize)
    (alpha : Array MQ 10#usize) (c : AspisR1PublicPreparation.r1_wire.Challenges)
    (out : MQ) (success : FIq_Terminal.terminal pub claims alpha c=ok (.Ok out))
    (hclaims : ∀ row∈claims.val,∀ x∈row.val,FIp_SemanticValues.Canon x)
    (halpha : ∀ x∈alpha.val,FIp_SemanticValues.Canon x)
    (hzc : ∀ x∈c.zc.val,FIp_SemanticValues.Canon x)
    (hmu : FIp_SemanticValues.Canon c.mu) :
    ∃ (selected : Array NQ 84#usize) (sem : FIr_TerminalTrace.SemPub)
      (comp h active g : NQ) (c1 : Array NQ 16#usize) (mask : Array NQ 10#usize),
      FIq_Native.array_from_fn_copy 84#usize FIq_Native.field.QM31.Insts.CoreMarkerCopy
        FIr_GatherCanonical.callback FIq_Native.field.QM31.ZERO (mapArray (mapArray toQ) claims)=ok selected ∧
      (∀ x∈selected.val,Canon x) ∧
      FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.semantic (toPublic pub)=ok sem ∧
      FIr_TerminalTrace.composition sem selected (mapArray toQ alpha) (toQ c.lambda) (toQ c.chi) (toQ c.theta)=
        ok (.Ok (comp,c1,mask,g,h,active)) ∧
      (Canon comp → Canon h → Canon active →
        FIp_SemanticValues.Canon out ∧ FIp_SemanticValues.decode out=FIr_TerminalValue.formula
          (R0P.SemSource.eqValue
            (fun j : Fin 10=>FIr_NativeArray.value (mapArray toQ c.zc) j.val)
            (fun j : Fin 10=>FIr_NativeArray.value (mapArray toQ alpha) j.val))
          (decode comp) (FIp_SemanticValues.decode c.mu) (decode h) (decode active)) := by
  obtain ⟨native,called,same⟩ := FIq_Terminal.reached pub claims alpha c out success
  obtain ⟨selected,sem,c1,mask,g,gather,semantic,parts⟩ := FIq_TerminalParts.reached
    (toPublic pub) (mapArray (mapArray toQ) claims) (mapArray toQ alpha) (toChallenges c) native called
  have canonical := FIr_GatherCanonical.gathered (mapArray (mapArray toQ) claims) selected
    (FIr_CarrierCanonical.claims claims hclaims) gather
  obtain ⟨comp,h,active,composition,value⟩ := FIr_TerminalPartsValue.reached_value
    sem selected (mapArray toQ alpha) (mapArray toQ c.zc) (toQ c.lambda) (toQ c.chi) (toQ c.theta)
    (toQ c.mu) native c1 mask g parts
    (FIr_CarrierCanonical.array c.zc hzc) (FIr_CarrierCanonical.array alpha halpha)
    ((FIr_CarrierCanonical.to_canon c.mu).mpr hmu)
  refine ⟨selected,sem,comp,h,active,g,c1,mask,gather,canonical,semantic,composition,?_⟩
  intro hc hh ha
  have result := value hc hh ha
  rw [← same]
  exact ⟨(FIr_CarrierCanonical.from_canon native).mpr result.1,by
    simpa only [FIr_CarrierCanonical.from_value,FIr_CarrierCanonical.to_value] using result.2⟩

#print axioms reached
end AspisR1.FIr_RootValue
end
