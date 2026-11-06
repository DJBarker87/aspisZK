import NJG_Results
import NJG_InputCarriers
set_option autoImplicit false
namespace AspisR1.NJG_CarrierBack
open Aeneas Aeneas.Std Result NJG_Carriers NJG_InputCarriers NJG_Results

theorem point (p : AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint) :
 upPoint (downPoint p)=p := by cases p;simp only [upPoint,downPoint,q_back]

theorem challenge (c : AspisR1PublicPreparation.r1_wire.Challenges) :
 upChallenge (downChallenge c)=c := by
 cases c
 simp only [upChallenge,downChallenge,q_back,map_inverse downQ upQ q_back]

theorem transcript {H : Type} (t : AspisR1PublicPreparation.r1_wire.SemanticTranscript H) :
 upTranscript (downTranscript t)=t := by cases t;rfl

theorem verified {H : Type} (v : AspisR1PublicPreparation.r1_semantic.Verified H) :
 upVerified (downVerified v)=v := by
 cases v
 simp only [upVerified,downVerified,challenge,transcript,
  map_inverse downQ upQ q_back,map_inverse downPoint upPoint point,
  map_inverse (mapA downQ) (mapA upQ) (map_inverse downQ upQ q_back)]

theorem result {H : Type}
 (r : Result (core.result.Result (AspisR1PublicPreparation.r1_semantic.Verified H) ME)) :
 upResult (downResult r)=r := by
 cases r with
 | fail error=>rfl
 | div=>rfl
 | ok reply=>cases reply <;> simp only [upResult,downResult,verified,error_back]

theorem prefix_back (p : AspisR1PublicPreparation.r1_wire.Prefix) : upPrefix (downPrefix p)=p := by cases p;rfl

theorem digest {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H) :
 upDigest (downDigest D)=D := by cases D;rfl

#print axioms point
#print axioms challenge
#print axioms transcript
#print axioms verified
#print axioms result
#print axioms prefix_back
#print axioms digest
end AspisR1.NJG_CarrierBack
