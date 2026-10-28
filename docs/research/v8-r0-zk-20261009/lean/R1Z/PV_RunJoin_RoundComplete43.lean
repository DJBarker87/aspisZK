import R1Z.PV_RunJoin_RoundAccum43
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundComplete43
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
open PV_RunJoin_RoundAccum43
variable [ExternalTypes]
abbrev Q := aspis_core.field.QM31

theorem rounds (ops : ExternalFuns) {H F : Type} (hash : aspis_core.digest.Digest32 H)
    (oi : host_sumcheck.Oracle F) (oracle : F) (n : Nat) (round : Usize)
    (transcript : host_wire.SemanticTranscript H) (out : alloc.vec.Vec U8)
    (point : Array Q 10#usize) (running : Q) (bound : round.val+n=10)
    (room : out.length+901*n≤Usize.max) :
    Post (Good out n) (@host_sumcheck.prove_sumcheck_rounds _ (ProverRwP6BodyCandidate.selected ops)
      H F hash oi transcript out point running round oracle) := by
  letI : ExternalFuns := ProverRwP6BodyCandidate.selected ops
  rw [PV_RunJoin_RoundThread38.thread hash oi oracle n round bound transcript out point running]
  exact PV_RunJoin_RoundAccum43.phase ops hash oi oracle n round transcript out point running bound room

theorem post (ops : ExternalFuns) {H F : Type} (hash : aspis_core.digest.Digest32 H)
    (oi : host_sumcheck.Oracle F) (oracle : F)
    (transcript : host_wire.SemanticTranscript H) (out : alloc.vec.Vec U8)
    (running : Q) (room : out.length+9010≤Usize.max) :
    Post (Good out 10) (@host_sumcheck.prove_sumcheck _ (ProverRwP6BodyCandidate.selected ops)
      H F hash oi transcript out running oracle) := by
  unfold host_sumcheck.prove_sumcheck
  apply PV_RunJoin_ResultPost41.bind
  intro zero
  exact rounds ops hash oi oracle 10 0#usize transcript out (Array.repeat 10#usize zero) running
    rfl (by simpa using room)
#print axioms rounds
#print axioms post
end R1Z.PV_RunJoin_RoundComplete43
