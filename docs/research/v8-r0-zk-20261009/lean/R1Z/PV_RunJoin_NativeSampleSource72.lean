import R1Z.PV_RunJoin_NativeSampleFields72
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeSampleSource72
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
variable {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)

theorem loop : @host_sumcheck.evaluate_assignment_loop (types base) (opsNative base heap box ops runtime world)=
    @host_sumcheck.evaluate_assignment_loop (types base) (@ProverRwDictionaryScalar.selected (types base) ops) := by
  letI : ExternalTypes := types base
  unfold host_sumcheck.evaluate_assignment_loop host_sumcheck.evaluate_assignment_loop.body
  rw [PV_RunJoin_NativeSampleFields72.one,PV_RunJoin_NativeQuarticTotal69.zero_source]
  rfl

theorem evaluate {T : Type} (oi : host_sumcheck.Oracle T) :
    @host_sumcheck.evaluate_assignment (types base) (opsNative base heap box ops runtime world) T oi=
      @host_sumcheck.evaluate_assignment (types base) (@ProverRwDictionaryScalar.selected (types base) ops) T oi := by
  letI : ExternalTypes := types base
  unfold host_sumcheck.evaluate_assignment
  rw [PV_RunJoin_NativeSampleFields72.complex,PV_RunJoin_NativeSampleFields72.quartic,loop]

theorem reached {T : Type} (oi : host_sumcheck.Oracle T) (oracle : T)
    (p : Nat → PV_RunJoin_SampleSource34.Raw) (round assignments i : Usize)
    (bound : round.val<10) (positive : assignments.val≠0) :
    ∃ sample assignment : Usize,
      sample.val=i.val/assignments.val ∧ assignment.val=i.val%assignments.val ∧
      @host_sumcheck.evaluate_assignment (types base) (opsNative base heap box ops runtime world)
        T oi oracle (PV_RunJoin_PointArray34.array p) round assignments i=
        oi.evaluate oracle (PV_RunJoin_PointArray34.array
          (ProverCommitSamplePoint49.point p round.val assignment (UScalar.cast .U32 sample))) := by
  letI : ExternalTypes := types base
  rw [evaluate]
  exact PV_RunJoin_SampleSource34.evaluate ops oi oracle p round assignments i bound positive

#print axioms loop
#print axioms evaluate
#print axioms reached
end R1Z.PV_RunJoin_NativeSampleSource72
