import R1Z.PV_RunJoin_NativeSumcheckArithmetic72
import R1Z.PV_RunJoin_NativeQuarticEq72
import R1Z.PV_RunJoin_RoundAfterPolynomial72
import R1Z.PV_RunJoin_ByteAppend38
import R1Z.PV_RunJoin_WeightArrayUpdate47
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeRoundContinuation72
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
abbrev Q := aspis_core.field.QM31

theorem complete {H S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (digest : aspis_core.digest.Digest32 H)
    (transcript next : host_wire.SemanticTranscript H) (output bytes framed : alloc.vec.Vec U8)
    (point : Array Q 10#usize) (round : Usize) (bound : round.val<10)
    (polynomial : Array Q 28#usize) (running challenge : Q)
    (boundary : @aspis_core.state_only_sumcheck.state_only_boundary_sum (types base)
      (opsNative base heap box ops runtime world) polynomial=ok running)
    (encoded : @host_sumcheck.encode_polynomial (types base)
      (opsNative base heap box ops runtime world) polynomial=ok bytes)
    (recorded : letI : ExternalTypes := types base
      letI : ExternalFuns := opsNative base heap box ops runtime world
      host_wire.record (U8.wrapping_add 15#u8 (UScalar.cast .U8 round))
        (alloc.vec.Vec.deref bytes)=ok (.Ok framed))
    (sampled : letI : ExternalTypes := types base
      letI : ExternalFuns := opsNative base heap box ops runtime world
      host_wire.SemanticTranscript.semantic digest transcript
        (U8.wrapping_add 15#u8 (UScalar.cast .U8 round))
        (alloc.vec.Vec.deref framed)=ok (.Ok challenge,next))
    (room : output.length+framed.length≤Usize.max) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    ∃ value after,PV_RunJoin_RoundAfterPolynomial72.run digest transcript output point running round polynomial=
      ok (.Ok (Aeneas.Std.Array.set point round challenge,value),next,after) ∧
      after.val=output.val++framed.val := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  have hp := PV_RunJoin_WeightArrayUpdate47.complete point round bound challenge
  obtain ⟨q,hq⟩ := ProverRwP6ArrayRead.read (Aeneas.Std.Array.set point round challenge) round bound
  obtain ⟨value,hvalue⟩ := PV_RunJoin_NativeSumcheckArithmetic72.evaluation
    base heap box ops runtime world polynomial q
  obtain ⟨after,ha,hval⟩ := PV_RunJoin_ByteAppend38.append output (alloc.vec.Vec.deref framed) room
  refine ⟨value,after,?_,hval⟩
  simp only [PV_RunJoin_RoundAfterPolynomial72.run,boundary,
    PV_RunJoin_NativeQuarticEq72.ne_self base heap box ops runtime world,
    encoded,recorded,sampled,hp,hq,hvalue,ha,lift,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch,Bool.false_eq_true,if_false,Aeneas.Std.uncurry]

#print axioms complete
end R1Z.PV_RunJoin_NativeRoundContinuation72
