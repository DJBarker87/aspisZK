import NMP_Install131
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_Install150
open Aeneas Aeneas.Std Result NMP_ResultTransport NMP_Transport

def toReply {H : Type} (r : core.result.Result NMP_prepare.aspis_core.state_only_prefix.r0.Challenges NMP_prepare.r1_wire.Error × NMP_prepare.r1_wire.SemanticTranscript H) :=
 (inner toT3 toT12 r.1,toT10 r.2)
def fromReply {H : Type} (r : core.result.Result AspisR1PublicPreparation.r1_wire.Challenges AspisR1PublicPreparation.r1_wire.Error × AspisR1PublicPreparation.r1_wire.SemanticTranscript H) :=
 (inner fromT3 fromT12 r.1,fromT10 r.2)

theorem reply_inverse {H : Type} (r : core.result.Result AspisR1PublicPreparation.r1_wire.Challenges AspisR1PublicPreparation.r1_wire.Error × AspisR1PublicPreparation.r1_wire.SemanticTranscript H) :
 toReply (fromReply r)=r := by
 rcases r with ⟨r,t⟩
 have er := inner_inverse fromT3 toT3 fromT12 toT12 fromT3_inverse fromT12_inverse r
 simp only [toReply,fromReply,er,fromT10_inverse]

/-- The post-transcript is carried on BOTH Rust Result arms. -/
def begin_ {H : Type} (d : NMP_prepare.aspis_core.digest.Digest32 H)
 (p : NMP_prepare.r1_wire.Prefix) (t : NMP_prepare.r1_wire.SemanticTranscript H) :=
 outer fromReply (AspisR1PublicPreparation.r1_wire.begin (NMP_Install131.digest d) (toT13 p) (toT10 t))

theorem same {H : Type} (d : NMP_prepare.aspis_core.digest.Digest32 H)
 (p : NMP_prepare.r1_wire.Prefix) (t : NMP_prepare.r1_wire.SemanticTranscript H) :
 outer toReply (begin_ d p t) =
 AspisR1PublicPreparation.r1_wire.begin (NMP_Install131.digest d) (toT13 p) (toT10 t) :=
 outer_inverse _ _ reply_inverse _
#print axioms reply_inverse
#print axioms same
end AspisR1.NMP_Install150
