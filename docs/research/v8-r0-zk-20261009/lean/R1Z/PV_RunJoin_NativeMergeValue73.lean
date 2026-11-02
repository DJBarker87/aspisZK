import R1Z.PV_RunJoin_SliceImage73
import R1Z.PV_RunJoin_MergeInstall35
import R1Z.PV_RunJoin_InterpolationFields72
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeMergeValue73
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
open PV_RunJoin_FieldData34 (value canonical)
open PV_RunJoin_SampleDomain34 (count assignments)
open scoped BigOperators
abbrev Q := aspis_core.field.QM31
variable {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)

theorem dictionary :
    @host_sumcheck.merge_evaluations (types base) (opsNative base heap box ops runtime world)=
    @host_sumcheck.merge_evaluations (types base)
      (@ProverRwP6BodyCandidate.selected (types base) (residual base ops runtime world)) := by
  unfold host_sumcheck.merge_evaluations host_sumcheck.merge_evaluations_loop
    host_sumcheck.merge_evaluations_loop.body
  simp only [aspis_core.field.QM31.ZERO,aspis_core.field.QM31.add,
    PV_RunJoin_InterpolationFields72.op64 base heap box ops runtime world,
    PV_RunJoin_InterpolationFields72.op67 base heap box ops runtime world]

theorem complete (r : Usize) (hr : r.val<10) (es : Nat → Q)
    (evaluations : Slice (core.result.Result Q r1_wire.Error))
    (size : evaluations.length=(count r).val)
    (agrees : ∀ i : Usize,i.val<(count r).val → Slice.index_usize evaluations i=ok (.Ok (es i.val)))
    (canonical : ∀ j,j<(count r).val → canonical (es j)) :
    ∃ out : Nat → Q,
      @host_sumcheck.merge_evaluations (types base) (opsNative base heap box ops runtime world)
        evaluations (assignments r)=ok (.Ok (PV_RunJoin_MergeArray35.array out)) ∧
      (∀ k,k<28 → PV_RunJoin_FieldData34.canonical (out k)) ∧
      ∀ k,value (out k)=∑ j ∈ Finset.range (count r).val,
        if j/(assignments r).val=k then value (es j) else 0 := by
  letI : ExternalTypes := types base
  have image := PV_RunJoin_SliceImage73.complete evaluations (count r) (fun j => core.result.Result.Ok (es j)) size agrees
  rw [dictionary,image]
  exact PV_RunJoin_MergeInstall35.installed (residual base ops runtime world) r hr es canonical

#print axioms dictionary
#print axioms complete
end R1Z.PV_RunJoin_NativeMergeValue73
