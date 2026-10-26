import SAP_AlphaTransport
import SAP_CoordinateTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_PreparedFields
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller.InstalledPreparation
open AspisR1ClaimPreparedBridge AspisR1CurrentPreparedClaim.Concrete

/-- Carrier transport only; all nine source facts must be supplied by the
successful-source producers, not by an owner contract. -/
theorem fields (out : verifier.Prepared)
    (variant : out.variant=.S2)
    (queries : ∀ j : Fin 22,(out.queries.val[j.val]'(by simpa [out.queries.property] using j.isLt)).val<262144)
    (gamma : Canonical (toClaimE out.gamma)) (kappa : Canonical (toClaimE out.kappa))
    (alpha : CanonicalAlphaPair out)
    (rho : Port3_FlushInstall.Canonical (Tx1Q_Carriers.k (currentQ out.rho)))
    (semanticAlpha : ∀ q ∈ out.semantic_alpha.val,SAP_CanonicalCarrier.CanonK q)
    (z0 z1 : aspis_core.circle.SecureCirclePoint) (z : out.z=Array.make 2#usize [z0,z1])
    (c0 : SAP_CanonicalCarrier.CanonK z0.x ∧ SAP_CanonicalCarrier.CanonK z0.y)
    (c1 : SAP_CanonicalCarrier.CanonK z1.x ∧ SAP_CanonicalCarrier.CanonK z1.y)
    (claim : Canonical (toClaimE out.claim)) :
    Port5Q2_Prepared.PreparedFields (Tx1Q_Carriers.prepared (currentPrepared out)) := by
  refine ⟨?_,queries,SAP_CanonicalCarrier.wide out.gamma gamma,
    SAP_CanonicalCarrier.wide out.kappa kappa,?_,rho,?_,?_,SAP_CanonicalCarrier.wide out.claim claim⟩
  · change Tx1Q_Carriers.variant (currentVariant out.variant)=_
    rw [variant];rfl
  · exact SAP_AlphaTransport.alpha out alpha
  · intro j
    change OraclePortCkptAbi4Decode.Canonical (CheckpointBytes3Namespaces.toK
      (Tx1Q_Carriers.k (currentQ (out.semantic_alpha.val[j.val]'_))))
    exact SAP_CanonicalCarrier.qm _ (semanticAlpha _ (List.getElem_mem _))
  · exact SAP_CoordinateTransport.coordinates out z0 z1 z c0 c1

#print axioms fields
end AspisR1.SAP_PreparedFields
end
