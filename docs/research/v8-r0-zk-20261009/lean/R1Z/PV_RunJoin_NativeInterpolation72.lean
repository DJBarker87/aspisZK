import R1Z.PV_RunJoin_InterpolationFields72
import R1Z.PV_RunJoin_InterpolationDictionary72
import R1Z.PV_RunJoin_InterpolationInput72
import R1Z.PV_RunJoin_InterpolationComplete38
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeInterpolation72
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
abbrev Q := aspis_core.field.QM31
variable {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)

theorem dictionary :
    @host_sumcheck.interpolate (types base) (opsNative base heap box ops runtime world)=
      @host_sumcheck.interpolate (types base)
        (@ProverRwP6BodyCandidate.selected (types base) (residual base ops runtime world)) := by
  letI : ExternalTypes := types base
  exact PV_RunJoin_InterpolationDictionary72.complete _ _
    (PV_RunJoin_InterpolationFields72.op55 base heap box ops runtime world)
    (PV_RunJoin_InterpolationFields72.op56 base heap box ops runtime world)
    (PV_RunJoin_InterpolationFields72.op57 base heap box ops runtime world)
    (PV_RunJoin_InterpolationFields72.op59 base heap box ops runtime world)
    (PV_RunJoin_InterpolationFields72.op64 base heap box ops runtime world)
    (PV_RunJoin_InterpolationFields72.op67 base heap box ops runtime world)
    (PV_RunJoin_InterpolationFields72.op70 base heap box ops runtime world)
    (PV_RunJoin_InterpolationFields72.op74 base heap box ops runtime world)

theorem complete (values : Array Q 28#usize) :
    ∃ out : Nat → Q,
      @host_sumcheck.interpolate (types base) (opsNative base heap box ops runtime world) values=
        ok (PV_RunJoin_MergeArray35.array out) ∧
      (∀ k,k<28 → PV_RunJoin_FieldData34.canonical (out k)) := by
  letI : ExternalTypes := types base
  rw [dictionary]
  obtain ⟨out,ho,hc,_⟩ := PV_RunJoin_InterpolationComplete38.interpolate
    (residual base ops runtime world) (PV_RunJoin_InterpolationInput72.cells values)
  rw [PV_RunJoin_InterpolationInput72.complete] at ho
  exact ⟨out,ho,hc⟩

#print axioms dictionary
#print axioms complete
end R1Z.PV_RunJoin_NativeInterpolation72
