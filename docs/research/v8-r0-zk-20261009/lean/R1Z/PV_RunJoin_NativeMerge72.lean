import R1Z.PV_RunJoin_MergeTotal72
import R1Z.PV_RunJoin_SampleDomain34
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeMerge72
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
open PV_RunJoin_SampleDomain34
abbrev Q := aspis_core.field.QM31

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (round : Usize) (bound : round.val<10)
    (evaluations : Slice (core.result.Result Q r1_wire.Error))
    (size : evaluations.length=(count round).val)
    (valid : ∀ (i : Usize),i.val<evaluations.length → ∃ q,Slice.index_usize evaluations i=ok (.Ok q)) :
    ∃ out,@host_sumcheck.merge_evaluations (types base)
      (opsNative base heap box ops runtime world) evaluations (assignments round)=ok (.Ok out) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  have positive := assignments_bound round bound
  have countval := count_value round bound
  apply PV_RunJoin_MergeTotal72.complete
    (PV_RunJoin_NativeQuarticTotal69.add base heap box ops runtime world)
    ⟨_,PV_RunJoin_NativeQuarticTotal69.zero_source base heap box ops runtime world⟩
    evaluations (assignments round) (Nat.ne_of_gt positive.1)
  · rw [size,countval];omega
  · intro j hj
    apply (Nat.div_lt_iff_lt_mul positive.1).mpr
    rw [size,countval] at hj
    simpa only [Nat.mul_comm] using hj
  · exact valid

#print axioms complete
end R1Z.PV_RunJoin_NativeMerge72
