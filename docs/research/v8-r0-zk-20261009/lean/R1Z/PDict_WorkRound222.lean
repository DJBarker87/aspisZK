import R1Z.PDict_WorkTransport222
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_WorkTransport222
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

theorem work_callbacks (ops : ExternalFuns) (hw : WorkExtensional ops)
    {H A B : Type} (digest : aspis_core.digest.Digest32 H)
    (oa : host_sumcheck.Oracle A) (ob : host_sumcheck.Oracle B) (a : A) (b : B)
    (h : ∀ p, oa.evaluate a p = ob.evaluate b p)
    (point : Array aspis_core.field.QM31 10#usize) (round assignments stage n : Usize) :
    @host_work.map _ ops _ _
      (@host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error _ ops H A digest oa)
      stage n (a, point, round, assignments) =
    @host_work.map _ ops _ _
      (@host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error _ ops H B digest ob)
      stage n (b, point, round, assignments) := by
  apply hw
  intro i
  exact assignment ops oa ob a b h point round assignments i

theorem round_transport (ops : ExternalFuns) (hw : WorkExtensional ops)
    {H A B : Type} (digest : aspis_core.digest.Digest32 H)
    (oa : host_sumcheck.Oracle A) (ob : host_sumcheck.Oracle B) (a : A) (b : B)
    (h : ∀ p, oa.evaluate a p = ob.evaluate b p)
    (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec U8)
    (point : Array aspis_core.field.QM31 10#usize) (running : aspis_core.field.QM31) (round : Usize) :
    @host_sumcheck.prove_sumcheck_round _ ops H A digest oa transcript output point running round a =
    @host_sumcheck.prove_sumcheck_round _ ops H B digest ob transcript output point running round b := by
  delta host_sumcheck.prove_sumcheck_round
  simp only [work_callbacks ops hw digest oa ob a b h]

#print axioms work_callbacks
#print axioms round_transport
end R1Z.PDict_WorkTransport222
