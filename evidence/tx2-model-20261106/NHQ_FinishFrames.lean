import NHQ_FinishPackets
import NHQ_WeightPort
set_option autoImplicit false
noncomputable section
namespace NHQ_FinishFrames
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open Port3_NativeFinishBody NGM_FinishControl NHQ_FinishRelationModel
variable {W : Type}

theorem round_error (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
 (folds : Usize) (error : verifier.Error) :
 afterRoundReply ops v p a obs folds (.Err error)=ok (.Err error) := by rfl

theorem weights_error (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
 (folds : Usize) (claim : E) (error : verifier.Error) :
 afterWeightsReply ops v p a obs folds claim (.Err error)=ok (.Err error) := by rfl

theorem pair_error (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
 (claim : E) (error : verifier.Error) :
 afterPairReply ops v p a obs claim (.Err error)=ok (.Err error) := by rfl

theorem dot_error (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit)) (error : verifier.Error) :
 afterDotReply ops v p a obs (.Err error)=ok (.Err error) := by rfl

/-- NGM's SAME post-flush accumulator supplies the dot's primitive width without a new premise. -/
theorem dot_width (a : verifier.Accumulator) (domain : NGM_FinishDomain.AccumulatorDomain a) :
 (NHQ_WeightPort.weights a.weights.deref).val.length≤64 := by
 rw [NHQ_WeightPort.width]
 change a.weights.val.length≤64
 exact Nat.le_of_eq domain.width

/-- The two actual returned round claims establish the later canonical-claim domains. -/
theorem round_claims (round0 round1 : Slice U8)
 (alpha0 alpha1 claim first last : LPi_FieldValues.NE)
 (ca0 : LPi_FieldValues.canonE alpha0) (ca1 : LPi_FieldValues.canonE alpha1)
 (r0 : NHE_Round.source round0 alpha0 claim=ok (.Ok first))
 (r1 : NHE_Round.source round1 alpha1 first=ok (.Ok last)) :
 LPi_FieldValues.canonE first ∧ LPi_FieldValues.canonE last :=
 ⟨NHQ_RoundDomain.output round0 alpha0 claim first ca0 r0,
  NHQ_RoundDomain.output round1 alpha1 first last ca1 r1⟩

#print axioms round_error
#print axioms weights_error
#print axioms pair_error
#print axioms dot_error
#print axioms dot_width
#print axioms round_claims
end NHQ_FinishFrames
