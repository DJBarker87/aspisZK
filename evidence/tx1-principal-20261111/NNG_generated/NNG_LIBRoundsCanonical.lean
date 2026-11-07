import NNG_Model134
import NNG_LIBArrayDomain
import LIB_VRoundCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LIBRoundsCanonical
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NNG_LIBScalar NNG_LIBArrayDomain
open AspisR1.NMT_Transport (arr)

/-- Canonicality is obtained from the deterministic source-model arm of
CLOSED134. No native cut, arbitrary chain reply, or success premise is added
to the caller domain: returned is the actual reached child return. -/
theorem returned (p : LIB_VCarriers.Prefix) (d : aspis_core.digest.Digest32 Unit)
    (t : r1_wire.SemanticTranscript Unit) (running : Q) (alpha : Alpha)
    (after : r1_wire.SemanticTranscript Unit)
    (success : NNG_Model134.rounds d (fromT12 (LIB_VCarriers.prefixRaw p)) t =
      .ok (.Ok (running,alpha,after))) :
    Domain running ∧ DomainArray alpha := by
  have selected := NNG_Model134.call_model d (fromT12 (LIB_VCarriers.prefixRaw p)) t
  rw [success] at selected
  have model : (AspisR1PublicPreparation.PreparedHashCode.run
      (AspisR1PublicPreparation.S1SemanticCode.rounds NJM_RoundJoin.R
        (NNG_Install.digest d) (LIB_VCarriers.prefixRaw p) (toT10 t))).2 =
      .ok (.Ok (toT1 running,arr toT1 alpha,toT10 after)) := by
    simpa only [NNG_Model134.model,fromT12_inverse,NNG_Model134.lowerReply,
      NMP_ResultTransport.outer,NMP_ResultTransport.inner] using selected.symm
  have canonical := LIB_VRoundCanonical.rounds p (NNG_Install.digest d) (toT10 t)
    (toT1 running,arr toT1 alpha,toT10 after) model
  refine ⟨canonical.1,?_⟩
  intro q member
  apply canonical.2 (toT1 q)
  exact List.mem_map.mpr ⟨q,member,rfl⟩
#print axioms returned
end AspisR1.NNG_LIBRoundsCanonical
