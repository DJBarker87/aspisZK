import RPv_FJn_NativeTerminal
import RPv_FJn_MainClaims
import RPv_FJn_MainPoint
import RPv_FJn_MainDecode
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_MainTerminal
open Aeneas Aeneas.Std Result
open FIq_Carriers
open FIz_ConcretePack (embed)
/-- Complete installed FIq body VALUE on its original main input carriers. -/
theorem value (pub : Public) (claims : Array (Array MQ 29#usize) 3#usize)
    (alpha : Array MQ 10#usize) (c : AspisR1PublicPreparation.r1_wire.Challenges) (out : MQ)
    (hc : ∀ row∈claims.val,∀ x∈row.val,FIp_SemanticValues.Canon x)
    (ha : ∀ x∈alpha.val,FIp_SemanticValues.Canon x)
    (hz : ∀ x∈c.zc.val,FIp_SemanticValues.Canon x)
    (hl : FIp_SemanticValues.Canon c.lambda) (hchi : FIp_SemanticValues.Canon c.chi)
    (ht : FIp_SemanticValues.Canon c.theta) (hm : FIp_SemanticValues.Canon c.mu)
    (bounds : FJa_PublicBounds.Bounds (FJa_PublicCopy.native pub))
    (run : FIq_Terminal.terminal pub claims alpha c=ok (.Ok out)) :
    FIp_SemanticValues.Canon out ∧ embed (FIp_SemanticValues.decode out)=
      R0P.SemSource.terminalValue (SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic (FJa_PublicCopy.native pub)))
        (embed (FIp_SemanticValues.decode c.lambda)) (embed (FIp_SemanticValues.decode c.chi))
        (embed (FIp_SemanticValues.decode c.theta)) (embed (FIp_SemanticValues.decode c.mu))
        (fun i=>embed (FJn_MainPoint.point c.zc i)) ConcretePackBasis.basis
        (fun j l=>embed (FJn_MainClaims.claims claims j l)) (fun i=>embed (FJn_MainPoint.point alpha i)) := by
  obtain ⟨native,called,same⟩:=FIq_Terminal.reached pub claims alpha c out run
  have cc:=FIr_CarrierCanonical.claims claims hc
  have ac:=FIr_CarrierCanonical.array alpha ha
  have zc:=FIr_CarrierCanonical.array c.zc hz
  have bound : FJa_PublicBounds.Bounds (FJa_PublicCopy.native (fromPublic (toPublic pub))) := by
    rw [public_roundtrip];exact bounds
  have got:=FJn_NativeTerminal.value (toPublic pub) (mapArray (mapArray toQ) claims) (mapArray toQ alpha)
    (toChallenges c) native cc ac zc hl hchi ht hm bound called
  rw [←same]
  refine ⟨(FIr_CarrierCanonical.from_canon native).mpr got.1,?_⟩
  have ce : (fun j l=>embed (FJn_GatherProjection.claims (mapArray (mapArray toQ) claims) j l))=
      (fun j l=>embed (FJn_MainClaims.claims claims j l)) := by
    funext j l;exact congrArg embed (FJn_MainClaims.value claims j l)
  simpa only [FIr_CarrierCanonical.from_value,FJn_NativeCarrierBridge.decode,public_roundtrip,
    toChallenges,FJn_MainDecode.value,FIr_CarrierCanonical.to_value,FJn_MainPoint.value,ce] using got.2
#print axioms value
end AspisR1.FJn_MainTerminal
end
