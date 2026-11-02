import R1Z.PV_RunJoin_RoundSequencePlan72
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SumcheckPlan72
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_Sequential64
variable [ExternalTypes] [ExternalFuns]

theorem complete {H T S F : Type} (runtime : PV_RunJoin_AllocatorWorld63.Runtime S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (digest : aspis_core.digest.Digest32 H) (oi : host_sumcheck.Oracle T)
    (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec U8)
    (initial : aspis_core.field.QM31) (oracle : T) :
    execute runtime (.step aspis_core.field.QM31.ZERO (fun zero =>
      PV_RunJoin_RoundSequencePlan72.phase digest oi 10 transcript output
        (Array.repeat 10#usize zero) initial 0#usize oracle)) world=
      (do let result ← host_sumcheck.prove_sumcheck digest oi transcript output initial oracle
          ok (result,world)) := by
  simp only [execute,host_sumcheck.prove_sumcheck,bind_assoc_eq]
  apply congrArg (Aeneas.Std.bind aspis_core.field.QM31.ZERO)
  funext zero
  rw [PV_RunJoin_RoundSequencePlan72.phase_execute,
    PV_RunJoin_RoundThread38.thread digest oi oracle 10 0#usize rfl]

#print axioms complete
end R1Z.PV_RunJoin_SumcheckPlan72
