import R1Z.PV_RunJoin_RoundThread38
import R1Z.PV_RunJoin_InterpolationComplete38
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SumcheckThread38
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

def zeroPoint : Array aspis_core.field.QM31 10#usize :=
  Array.repeat 10#usize PV_RunJoin_InterpolationComplete38.zero

/-- The actual sumcheck entry initializes the point once and then threads all
ten source rounds and the final oracle comparison. No semantic-terminal
meaning, worker purity or native runtime association is inferred. -/
theorem source (ops : ExternalFuns) {H F : Type} (digest : aspis_core.digest.Digest32 H)
    (oi : host_sumcheck.Oracle F) (oracle : F) (transcript : host_wire.SemanticTranscript H)
    (output : alloc.vec.Vec U8) (initial : aspis_core.field.QM31) :
    @host_sumcheck.prove_sumcheck _ (ProverRwP6BodyCandidate.selected ops)
      H F digest oi transcript output initial oracle =
    @PV_RunJoin_RoundThread38.phase _ (ProverRwP6BodyCandidate.selected ops)
      H F digest oi 10 transcript output zeroPoint initial 0#usize oracle := by
  have hz : @aspis_core.field.QM31.ZERO _ (ProverRwP6BodyCandidate.selected ops)=
      .ok PV_RunJoin_InterpolationComplete38.zero := by
    change Result.ok (ProverRwDictionaryTower.fromQ AspisR1ProducerRelease47.field.QM31.ZERO)=_
    rw [AspisR1ProducerRelease47.field.QM31.ZERO]
    rfl
  unfold host_sumcheck.prove_sumcheck
  rw [hz]
  simp only [bind_tc_ok]
  exact @PV_RunJoin_RoundThread38.thread _ (ProverRwP6BodyCandidate.selected ops)
    H F digest oi oracle 10 0#usize rfl transcript output zeroPoint initial

#print axioms source
end R1Z.PV_RunJoin_SumcheckThread38
