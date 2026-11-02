import R1Z.PV_RunJoin_NativePolynomialRecord73
import R1Z.PV_RunJoin_NativeSemanticSample73
import R1Z.PV_RunJoin_NativeRoundShape73
import R1Z.PV_RunJoin_NativeRoundContinuation72
import R1Z.PV_RunJoin_RoundRow73
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeRoundTail73
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
abbrev Q := aspis_core.field.QM31
abbrev T := host_wire.SemanticTranscript aspis_core.digest.LegacyHashFn

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (transcript : T) (output : alloc.vec.Vec U8) (point : Array Q 10#usize)
    (round : Usize) (bound : round.val<10) (polynomial : Array Q 28#usize) (running : Q)
    (boundary : @aspis_core.state_only_sumcheck.state_only_boundary_sum (types base)
      (opsNative base heap box ops runtime world) polynomial=ok running)
    (order : PV_RunJoin_RoundRow73.row round=transcript.next_row)
    (total : ∀ parts,∃ b,transcript.hash parts=ok b)
    (outputSize : output.length=171+901*round.val) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    ∃ challenge value next after,
      PV_RunJoin_RoundAfterPolynomial72.run aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
        transcript output point running round polynomial=
        ok (.Ok (Aeneas.Std.Array.set point round challenge,value),next,after) ∧
      next.next_row.val=16+round.val ∧ next.hash=transcript.hash ∧
      after.length=171+901*(round.val+1) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  have rowval := PV_RunJoin_RoundRow73.value round (by omega)
  have shape := PV_RunJoin_NativeRoundShape73.complete base heap box ops runtime world
    (PV_RunJoin_RoundRow73.row round) (by rw [rowval];omega) (by rw [rowval];omega)
  obtain ⟨bytes,encoded,payload,blen⟩ := PV_RunJoin_NativePolynomialBytes72.complete
    base heap box ops runtime world polynomial
  obtain ⟨framed,recorded,frame,flen,parsed⟩ := PV_RunJoin_NativePolynomialRecord73.complete
    base heap box ops runtime world (PV_RunJoin_InterpolationInput72.cells polynomial)
    (alloc.vec.Vec.deref bytes) (PV_RunJoin_RoundRow73.row round) 2#u8 shape payload
  obtain ⟨challenge,next,sampled,nextRow,nextHash⟩ := PV_RunJoin_NativeSemanticSample73.complete
    base heap box ops runtime world transcript (PV_RunJoin_RoundRow73.row round)
    (alloc.vec.Vec.deref framed) (alloc.vec.Vec.deref bytes) order
    (by rw [rowval];omega) total parsed
  obtain ⟨value,after,run,afterval⟩ := PV_RunJoin_NativeRoundContinuation72.complete
    base heap box ops runtime world aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
    transcript next output bytes framed point round bound polynomial running challenge
    boundary encoded recorded sampled (by
      rw [outputSize,flen]
      have cap := PV_RunJoin_RoundRow73.capacity
      omega)
  refine ⟨challenge,value,next,after,run,?_,nextHash,?_⟩
  · rw [nextRow,PV_RunJoin_RoundRow73.next round (by omega)]
  · change after.val.length=171+901*(round.val+1)
    rw [afterval,List.length_append]
    change output.length+framed.length=171+901*(round.val+1)
    rw [outputSize,flen]
    omega

#print axioms complete
end R1Z.PV_RunJoin_NativeRoundTail73
