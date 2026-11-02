import R1Z.PV_RunJoin_NativeInterpolationValue73
import R1Z.PV_RunJoin_NativeBoundaryValue73
import R1Z.PV_RunJoin_CanonicalInjective73
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeInterpolationBoundary73
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
open PV_RunJoin_FieldData34 (value canonical)
abbrev Q := aspis_core.field.QM31
variable {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)

theorem complete (values : Array Q 28#usize) :
    ∃ polynomial : Nat → Q,
      @host_sumcheck.interpolate (types base) (opsNative base heap box ops runtime world) values=
        ok (PV_RunJoin_MergeArray35.array polynomial) ∧
      (∀ k,k<28 → canonical (polynomial k)) ∧ ∃ boundary,
      @aspis_core.state_only_sumcheck.state_only_boundary_sum (types base)
        (opsNative base heap box ops runtime world) (PV_RunJoin_MergeArray35.array polynomial)=ok boundary ∧
      canonical boundary ∧ value boundary=value (PV_RunJoin_InterpolationInput72.cells values 0)+
        value (PV_RunJoin_InterpolationInput72.cells values 1) := by
  obtain ⟨p,hi,hc,hs⟩ := PV_RunJoin_NativeInterpolationValue73.complete base heap box ops runtime world values
  obtain ⟨q,hq,hcq,hv⟩ := PV_RunJoin_NativeBoundaryValue73.complete base heap box ops runtime world p
  have zero := hs ⟨0,by decide⟩
  have one := hs ⟨1,by decide⟩
  simp only [Fin.val_mk,Nat.cast_zero] at zero
  simp only [Fin.val_mk,Nat.cast_one] at one
  exact ⟨p,hi,hc,q,hq,hcq,by rw [hv,zero,one]⟩

theorem running (values : Array Q 28#usize) (claim : Q) (hclaim : canonical claim)
    (sum : value claim=value (PV_RunJoin_InterpolationInput72.cells values 0)+
      value (PV_RunJoin_InterpolationInput72.cells values 1)) :
    ∃ polynomial : Nat → Q,
      @host_sumcheck.interpolate (types base) (opsNative base heap box ops runtime world) values=
        ok (PV_RunJoin_MergeArray35.array polynomial) ∧
      @aspis_core.state_only_sumcheck.state_only_boundary_sum (types base)
        (opsNative base heap box ops runtime world) (PV_RunJoin_MergeArray35.array polynomial)=ok claim := by
  obtain ⟨p,hi,hc,q,hq,hcq,hv⟩ := complete base heap box ops runtime world values
  have eq := PV_RunJoin_CanonicalInjective73.complete q claim hcq hclaim (hv.trans sum.symm)
  exact ⟨p,hi,hq.trans (congrArg Result.ok eq)⟩

#print axioms complete
#print axioms running
end R1Z.PV_RunJoin_NativeInterpolationBoundary73
