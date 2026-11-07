import NNG_LegacyConfig136
import NNG_InstallClaims
import NNG_InstallRecord
import NNG_InstallPayload
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LegacyCalls136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NMP_ResultTransport (outer inner)
open NMT_Transport (arr)

theorem rounds {H : Type} (d : aspis_core.digest.Digest32 H) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) :
 outer (inner NNG_Model134.lowerReply toT13) (NNG_Model134.rounds d p t)=
 AspisR1PublicPreparation.RoundModel.rounds AspisS1ExtractedRoundChildren.children
   (NNG_Install.digest d) (toT12 p) (toT10 t) := by
 rw [NNG_Model134.call_model,NNG_Model134.model,AspisR1PublicPreparation.PreparedHashCode.run_value,
   AspisR1PublicPreparation.S1SemanticCode.rounds_erasure,NNG_LegacyConfig136.rounds]

theorem circle {H : Type} (env : RSL.Env) (d : aspis_core.digest.Digest32 H)
 (t : r1_wire.SemanticTranscript H) (r : r1_wire.ValidatedRecord) :
 outer NNG_ModelCircle.lowerReply (NNG_ModelCircle.call d t r)=
 AspisR1PublicPreparation.FinishModel.circle_validated (NNG_LegacyConfig136.boundaries env)
  (NNG_Install.digest d) (toT10 t) (toT14 r) := by
 rw [NNG_ModelCircle.call_model]
 have original := congrArg Prod.snd (NJM_CircleCode.original (NNG_LegacyConfig136.boundaries env)
   (NNG_Install.digest d) (toT10 t) (toT14 r))
 rw [AspisR1PublicPreparation.PreparedHashCode.run_value,
   AspisR1PublicPreparation.S1SemanticCode.circleValidated_erasure] at original
 exact original.symm

theorem decode (n : Usize) (r : r1_wire.ValidatedRecord) (off : Usize) :
 outer (inner (arr toT1) toT13) (NNG_ModelDecode.call n r off)=
 AspisS1ExtractedRoundChildren.children.decode n (toT14 r) off := NNG_ModelDecode.call_model n r off

theorem claims (env : RSL.Env) (p : r1_wire.Prefix) :
 outer (inner NNG_InstallClaims.lowerClaims toT13) (NNG_LIBClaims.call env p)=
 (NNG_LegacyConfig136.boundaries env).claims (toT12 p) :=
 NNG_InstallClaims.same (NNG_LIBClaims.reservation env) p
#print axioms rounds
#print axioms circle
#print axioms decode
#print axioms claims
end AspisR1.NNG_LegacyCalls136
