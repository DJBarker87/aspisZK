import NNG_ModelHead136
import NNG_LIBRoundsCanonical
import NNG_DecodeReturned136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LegacyReturnMaps136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NMP_ResultTransport (outer inner)
open NMT_Transport (arr arr_inverse)

theorem rounds {H : Type} (d : aspis_core.digest.Digest32 H) (p : r1_wire.Prefix)
 (t : r1_wire.SemanticTranscript H) (running : AspisR1PublicPreparation.aspis_core.field.QM31)
 (alpha : Alpha) (after : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
 (returned : AspisR1PublicPreparation.RoundModel.rounds AspisS1ExtractedRoundChildren.children
   (NNG_Install.digest d) (toT12 p) (toT10 t)=.ok (.Ok (running,arr toT1 alpha,after))) :
 NNG_Model134.rounds d p t=.ok (.Ok (fromT1 running,alpha,fromT10 after)) := by
 unfold NNG_Model134.rounds NNG_Model134.model
 rw [AspisR1PublicPreparation.PreparedHashCode.run_value,
   AspisR1PublicPreparation.S1SemanticCode.rounds_erasure,NNG_LegacyConfig136.rounds,returned]
 simp only [outer,NMP_ResultTransport.inner,NNG_Model134.raiseReply]
 rw [arr_inverse toT1 fromT1 toT1_inverse]

theorem claims (env : RSL.Env) (p : r1_wire.Prefix) (claims : Claims)
 (returned : (NNG_LegacyConfig136.boundaries env).claims (toT12 p)=
   .ok (.Ok (NNG_InstallClaims.lowerClaims claims))) :
 NNG_LIBClaims.call env p=.ok (.Ok claims) := by
 unfold NNG_LIBClaims.call NNG_InstallClaims.claims
 change outer (NMP_ResultTransport.inner NNG_InstallClaims.raiseClaims fromT13)
   ((NNG_LegacyConfig136.boundaries env).claims (toT12 p))=_
 rw [returned]
 simp only [outer,NMP_ResultTransport.inner,NNG_InstallClaims.raiseClaims,NNG_InstallClaims.lowerClaims]
 congr 2
 apply arr_inverse
 intro row
 exact arr_inverse toT1 fromT1 toT1_inverse row

theorem decode (n : Usize) (r : AspisR1PublicPreparation.r1_wire.ValidatedRecord) (off : Usize)
 (a : Array Q n) (returned : AspisS1ExtractedRoundChildren.children.decode n r off=.ok (.Ok (arr toT1 a))) :
 NNG_ModelDecode.call n (fromT14 r) off=.ok (.Ok a) := by
 unfold NNG_ModelDecode.call
 rw [fromT14_inverse]
 change outer (NMP_ResultTransport.inner (arr fromT1) fromT13)
   (AspisS1ExtractedRoundChildren.children.decode n r off)=_
 rw [returned]
 simp only [outer,NMP_ResultTransport.inner]
 rw [arr_inverse toT1 fromT1 toT1_inverse]
#print axioms rounds
#print axioms claims
#print axioms decode
end AspisR1.NNG_LegacyReturnMaps136
