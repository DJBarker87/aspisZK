import NIT_FinishArguments
import NHQ_WeightPort
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFinishDot
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2

/-- The final dot packet uses the actual accumulator slice. Its native width
precondition follows from the retained SAME-call finish domain. -/
theorem source (proof : Slice U8) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (domain : NIG_FinishInput.Domain proof v p a) :
 NHQ_PacketPorts.dot v.final_message (NHQ_WeightPort.weights a.weights.deref)=
 SAG_DotClosed.source v.final_message a.weights.deref := by
 have width : (NHQ_WeightPort.weights a.weights.deref).val.length≤64 := by
  rw [NHQ_WeightPort.width]
  change a.weights.val.length≤64
  exact Nat.le_of_eq domain.accumulator.width
 exact (NHQ_PacketPorts.dot_packet _ _ width).trans
  (congrArg (SAG_DotClosed.source v.final_message) (NHQ_WeightPort.same a.weights.deref))

/-- Log argument binding and complete dot law at one reached site. The theorem
has no assertion that an unconstrained opaque seed is the dot's result. -/
theorem reached (proof : Slice U8) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (domain : NIG_FinishInput.Domain proof v p a)
 (round0 round1 alpha semanticAlpha z message owner weights : Nat)
 (l : FinishLog) (out : Reply Unit)
 (cut : cutFinishLog v p a round0 round1 alpha semanticAlpha z message owner weights l out)
 (entered : 6≤l.count) :
 l.dot_f=message ∧ l.dot_weights=weights ∧
 NHQ_PacketPorts.dot v.final_message (NHQ_WeightPort.weights a.weights.deref)=
 SAG_DotClosed.source v.final_message a.weights.deref := by
 obtain ⟨msg,ws,_,_⟩ := NIT_FinishArguments.dot v p a round0 round1 alpha semanticAlpha z message owner weights l out cut entered
 have hm : l.dot_f=message := by
  by_contra different
  simp only [NIT_RefInterpretation.decode,if_neg different] at msg
  cases msg
 have hw : l.dot_weights=weights := by
  by_contra different
  simp only [NIT_RefInterpretation.decode,if_neg different] at ws
  cases ws
 exact ⟨hm,hw,source proof v p a domain⟩

#print axioms source
#print axioms reached
end AspisR1.NIW_AlignFinishDot
