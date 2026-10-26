import R1Z.PDict_WorkRound222
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_WorkTransport222
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

theorem rounds_transport (ops : ExternalFuns) (hw : WorkExtensional ops)
    {H A B : Type} (digest : aspis_core.digest.Digest32 H)
    (oa : host_sumcheck.Oracle A) (ob : host_sumcheck.Oracle B) (a : A) (b : B)
    (h : ∀ p, oa.evaluate a p = ob.evaluate b p)
    (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec U8)
    (point : Array aspis_core.field.QM31 10#usize) (running : aspis_core.field.QM31) (round : Usize) :
    @host_sumcheck.prove_sumcheck_rounds _ ops H A digest oa transcript output point running round a =
    @host_sumcheck.prove_sumcheck_rounds _ ops H B digest ob transcript output point running round b := by
  have hm : @host_sumcheck.prove_sumcheck_rounds.mutual _ ops H A digest oa a =
      @host_sumcheck.prove_sumcheck_rounds.mutual _ ops H B digest ob b := by
    delta host_sumcheck.prove_sumcheck_rounds.mutual
    apply PDict_Static222.fixed_equal
    funext recur t o p r i
    simp only [h, round_transport ops hw digest oa ob a b h]
  delta host_sumcheck.prove_sumcheck_rounds
  rw [hm]

theorem sumcheck_transport (ops : ExternalFuns) (hw : WorkExtensional ops)
    {H A B : Type} (digest : aspis_core.digest.Digest32 H)
    (oa : host_sumcheck.Oracle A) (ob : host_sumcheck.Oracle B) (a : A) (b : B)
    (h : ∀ p, oa.evaluate a p = ob.evaluate b p)
    (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec U8)
    (initial : aspis_core.field.QM31) :
    @host_sumcheck.prove_sumcheck _ ops H A digest oa transcript output initial a =
    @host_sumcheck.prove_sumcheck _ ops H B digest ob transcript output initial b := by
  delta host_sumcheck.prove_sumcheck
  simp only [rounds_transport ops hw digest oa ob a b h]

#print axioms rounds_transport
#print axioms sumcheck_transport
end R1Z.PDict_WorkTransport222
