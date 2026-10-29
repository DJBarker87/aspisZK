import R1Z.PV_RunJoin_FinishArithmeticTrace63
import R1Z.PV_RunJoin_NativeFinishCanonical63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeFinalFold63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
abbrev W := aspis_core.field.wide_exact.WideExact

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (phase : PV_RunJoin_NativeActual63.P base heap box ops runtime world)
    (prepared : prover.PreparedOpening) (salts : host_commitment.PrivateSalts) (p : prover.Publication)
    (hp : letI : ExternalTypes := types base
      @prover.prepare_opening (types base) (opsNative base heap box ops runtime world)
      .S2 phase.val.hash phase.val.backend phase.val.sem=ok (.Ok prepared))
    (hs : letI : ExternalTypes := types base
      @prover.derive_private_salts (types base) (opsNative base heap box ops runtime world)
      phase.val.salts.1 phase.val.salts.2 phase.val.hash 114#u8=ok (.Ok salts))
    (hf : letI : ExternalTypes := types base
      @prover.finish_opening (types base) (opsNative base heap box ops runtime world)
      .S2 phase.val.hash prepared salts=ok (.Ok p)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    ∃ (second : Array W 7#usize) (final : alloc.vec.Vec W),
      prover.round (alloc.vec.Vec.deref prepared.q1) (alloc.vec.Vec.deref prepared.w1)=ok second ∧
      prover.encoded_slice (Array.to_slice second)=ok p.c1bytes ∧
      prover.fold (alloc.vec.Vec.deref prepared.q1)
        (ProverRwDictionaryTower.fromW (ProverCommitWideOps48.source (PV_RunJoin_ActualRun.data phase.val).b))
        false=ok final ∧
      prover.encoded_slice (alloc.vec.Vec.deref final)=ok p.fbytes ∧
      ProverCommitWideOps48.canonical (PV_RunJoin_ActualRun.data phase.val).b := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  obtain ⟨second,alpha,next,payload0,payload,final,hsecond,hcbytes,hpayload0,hpayload,hscalar,halpha,hb,hfinal,hfbytes⟩ :=
    @PV_RunJoin_FinishArithmeticTrace63.complete (types base) (opsNative base heap box ops runtime world)
      phase.val prepared salts p hp hs hf
  refine ⟨second,final,hsecond,hcbytes,?_,hfbytes,?_⟩
  · rw [hb];exact hfinal
  · exact (PV_RunJoin_NativeFinishCanonical63.complete base heap box ops runtime world phase.val prepared hp).2.2.2

#print axioms complete
end R1Z.PV_RunJoin_NativeFinalFold63
