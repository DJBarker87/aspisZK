import R1Z.PV_RunJoin_NativeQuarticTotal69
import R1Z.PV_RunJoin_InterpolationInput72
import R1Z.PV_RunJoin_PolyComplete38
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativePolynomialBytes72
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
abbrev Q := aspis_core.field.QM31
variable {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)

theorem embed : @ExternalFuns.op45 (types base) (opsNative base heap box ops runtime world)=
    @ExternalFuns.op45 (types base) (@ProverRwP6BodyCandidate.selected (types base) (residual base ops runtime world)) := by
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  exact PV_B2_F_RawNative.preserved_45 (PV_RunJoin_NativeResidual62.baseTypes base) heap box _

theorem serializer : @ExternalFuns.op51 (types base) (opsNative base heap box ops runtime world)=
    @ExternalFuns.op51 (types base) (@ProverRwP6BodyCandidate.selected (types base) (residual base ops runtime world)) := by
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  exact PV_B2_F_RawNative.preserved_51 (PV_RunJoin_NativeResidual62.baseTypes base) heap box _

theorem dictionary :
    @host_sumcheck.encode_polynomial (types base) (opsNative base heap box ops runtime world)=
      @host_sumcheck.encode_polynomial (types base)
        (@ProverRwP6BodyCandidate.selected (types base) (residual base ops runtime world)) := by
  unfold host_sumcheck.encode_polynomial host_sumcheck.encode_polynomial_loop host_sumcheck.encode_polynomial_loop.body
  simp only [aspis_core.field.wide_exact.WideExact.from_qm31,aspis_core.field.wide_exact.WideExact.to_le_bytes,
    embed base heap box ops runtime world,serializer base heap box ops runtime world]

theorem complete (values : Array Q 28#usize) :
    ∃ bytes,@host_sumcheck.encode_polynomial (types base) (opsNative base heap box ops runtime world) values=ok bytes ∧
      bytes.val=PV_RunJoin_PolyLoop38.payload (PV_RunJoin_InterpolationInput72.cells values) 0 28 ∧ bytes.val.length=896 := by
  letI : ExternalTypes := types base
  rw [dictionary]
  obtain ⟨bytes,hb,hv,hl⟩ := PV_RunJoin_PolyComplete38.encode (residual base ops runtime world)
    (PV_RunJoin_InterpolationInput72.cells values)
  change @host_sumcheck.encode_polynomial (types base)
    (@ProverRwP6BodyCandidate.selected (types base) (residual base ops runtime world))
      (PV_RunJoin_MergeArray35.array (PV_RunJoin_InterpolationInput72.cells values))=ok bytes at hb
  rw [PV_RunJoin_InterpolationInput72.complete] at hb
  exact ⟨bytes,hb,hv,hl⟩

#print axioms embed
#print axioms serializer
#print axioms dictionary
#print axioms complete
end R1Z.PV_RunJoin_NativePolynomialBytes72
