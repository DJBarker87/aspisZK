import NBR_SemanticFinish
set_option autoImplicit false
namespace AspisR1.NCA_ObserverErasure
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- The adopted default-feature finish uses the observer only in four marks,
all of which are pure no-ops. This is entire-Result erasure for arbitrary
boundaries and digest dictionaries, not an acceptance-only fixture fact. -/
theorem finish (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
    (transcript : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (left right : Option (verifier.Phase → Result Unit)) :
    FinishModel.finish R B D pub pre transcript challenges left =
      FinishModel.finish R B D pub pre transcript challenges right := by
  simp only [FinishModel.finish,VerifyPrefix.mark]

/-- The complete prefix has the same default-feature observer erasure. -/
theorem source (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8)
    (hash : H) (left right : Option (verifier.Phase → Result Unit)) :
    VerifyPrefix.verify (FinishModel.finish R B) D pub bytes hash left =
      VerifyPrefix.verify (FinishModel.finish R B) D pub bytes hash right := by
  simp only [VerifyPrefix.verify,FinishModel.finish,VerifyPrefix.mark]

#print axioms finish
#print axioms source
end AspisR1.NCA_ObserverErasure
