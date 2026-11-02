import R1Z.PV_RunJoin_NativeWorkerMerge72
import R1Z.PV_RunJoin_NativeInterpolation72
import R1Z.PV_RunJoin_NativePolynomialBytes72
import R1Z.PV_RunJoin_RoundAfterPolynomial72
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeRoundPolynomial72
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
open PV_RunJoin_SampleDomain34
abbrev Q := aspis_core.field.QM31

theorem complete {T H S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (digest : aspis_core.digest.Digest32 H)
    (oi : host_sumcheck.Oracle T) (oracle : T) (point : Array Q 10#usize)
    (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec U8)
    (running : Q) (round : Usize) (bound : round.val<10)
    (evaluations : alloc.vec.Vec (core.result.Result Q r1_wire.Error))
    (worker : letI : ExternalTypes := types base
      letI : ExternalFuns := opsNative base heap box ops runtime world
      @host_work.map (types base) ops _ _
        (host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error digest oi)
        (Usize.wrapping_add 100#usize round) (count round)
        (oracle,point,round,assignments round)=ok evaluations)
    (size : evaluations.length=(count round).val)
    (agrees : ∀ i : Usize,i.val<evaluations.length →
      Slice.index_usize (alloc.vec.Vec.deref evaluations) i=
        @host_sumcheck.evaluate_assignment (types base) (opsNative base heap box ops runtime world)
          T oi oracle point round (assignments round) i)
    (evaluates : ∀ p,∃ q,oi.evaluate oracle p=ok (.Ok q)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    ∃ (polynomial : Nat → Q) (bytes : alloc.vec.Vec U8),
      host_sumcheck.prove_sumcheck_round digest oi transcript output point running round oracle=
        PV_RunJoin_RoundAfterPolynomial72.run digest transcript output point running round
          (PV_RunJoin_MergeArray35.array polynomial) ∧
      (∀ k,k<28 → PV_RunJoin_FieldData34.canonical (polynomial k)) ∧
      host_sumcheck.encode_polynomial (PV_RunJoin_MergeArray35.array polynomial)=ok bytes ∧
      bytes.val.length=896 := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  obtain ⟨values,hmap,hmerge⟩ := PV_RunJoin_NativeWorkerMerge72.complete base heap box ops runtime world
    digest oi oracle point round bound evaluations worker size agrees evaluates
  obtain ⟨polynomial,hi,hcanonical⟩ := PV_RunJoin_NativeInterpolation72.complete
    base heap box ops runtime world values
  obtain ⟨bytes,hbytes,hpayload,hlen⟩ := PV_RunJoin_NativePolynomialBytes72.complete
    base heap box ops runtime world (PV_RunJoin_MergeArray35.array polynomial)
  refine ⟨polynomial,bytes,?_,hcanonical,hbytes,hlen⟩
  rw [PV_RunJoin_RoundWorkerReached69.reached]
  simp only [count,assignments,remaining] at hmap
  simp only [PV_RunJoin_NativeQuarticTotal69.zero_source base heap box ops runtime world,hmap,bind_tc_ok]
  exact PV_RunJoin_RoundAfterPolynomial72.reached digest transcript output point running round
    (assignments round) evaluations values (PV_RunJoin_MergeArray35.array polynomial) hmerge hi

#print axioms complete
end R1Z.PV_RunJoin_NativeRoundPolynomial72
