import SAP_CanonicalCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_CoordinateTransport
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller.InstalledPreparation
open AspisR1ClaimPreparedBridge

theorem coordinates (out : verifier.Prepared)
    (z0 z1 : aspis_core.circle.SecureCirclePoint) (z : out.z=Array.make 2#usize [z0,z1])
    (c0 : SAP_CanonicalCarrier.CanonK z0.x ∧ SAP_CanonicalCarrier.CanonK z0.y)
    (c1 : SAP_CanonicalCarrier.CanonK z1.x ∧ SAP_CanonicalCarrier.CanonK z1.y) :
    let p := Tx1Q_Carriers.prepared (currentPrepared out)
    ∀ j : Fin 4,OraclePortCkptAbi4Decode.Canonical (CheckpointBytes3Namespaces.toK (match j.val with
      | 0 => (p.z.val[0]'(by simp [p.z.property])).x
      | 1 => (p.z.val[0]'(by simp [p.z.property])).y
      | 2 => (p.z.val[1]'(by simp [p.z.property])).x
      | _ => (p.z.val[1]'(by simp [p.z.property])).y)) := by
  dsimp only
  intro j
  fin_cases j <;>
    simp only [Tx1Q_Carriers.prepared,currentPrepared,AspisR1ClaimPreparedBridge.mapArray,
      Tx1Q_Carriers.arr,List.getElem_map,z]
  · exact SAP_CanonicalCarrier.qm _ c0.1
  · exact SAP_CanonicalCarrier.qm _ c0.2
  · exact SAP_CanonicalCarrier.qm _ c1.1
  · exact SAP_CanonicalCarrier.qm _ c1.2

#print axioms coordinates
end AspisR1.SAP_CoordinateTransport
end
