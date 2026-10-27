import R1Z.PV_CB3_StagedGammaRank
import R1Z.PV_CB3_DigitInjective
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_GammaInjective
open Aeneas Aeneas.Std Result ProverRwFull
open PV_CB3_StagedGammaRank

theorem array_values {a b : Array U32 8#usize}
    (h : a.val.map UScalar.val = b.val.map UScalar.val) : a = b := by
  apply Subtype.ext
  exact (List.map_inj_right (f := fun x : U32 => x.val)
    (fun _ _ hv => UScalar.eq_of_val_eq hv)).mp h

theorem raw_injective {a b : Array U32 8#usize}
    (h : PV_CB3_StagedUnpack.raw a = PV_CB3_StagedUnpack.raw b) : a = b := by
  apply array_values
  simpa only [PV_CB3_StagedUnpack.raw_values] using congrArg PV_CB3_StagedUnpack.values h

theorem kernel_value_injective (a b : Array U32 8#usize)
    (h : PV_CB3_SamplerCarry.value PV_CB3_SamplerWord.base
        ((PV_CB3_StagedKernel.pipeline a).val.map UScalar.val) =
      PV_CB3_SamplerCarry.value PV_CB3_SamplerWord.base
        ((PV_CB3_StagedKernel.pipeline b).val.map UScalar.val)) :
    PV_CB3_StagedKernel.pipeline a = PV_CB3_StagedKernel.pipeline b := by
  apply array_values
  apply PV_CB3_DigitInjective.value_injective PV_CB3_SamplerWord.base
    (by unfold PV_CB3_SamplerWord.base; omega)
  · simp only [List.length_map,(PV_CB3_StagedKernel.pipeline a).property,
      (PV_CB3_StagedKernel.pipeline b).property]
  · intro d hd
    rcases List.mem_map.mp hd with ⟨x,hx,rfl⟩
    exact PV_CB3_StagedValue.kernel_canonical a x hx
  · intro d hd
    rcases List.mem_map.mp hd with ⟨x,hx,rfl⟩
    exact PV_CB3_StagedValue.kernel_canonical b x hx
  · exact h

#print axioms array_values
#print axioms raw_injective
#print axioms kernel_value_injective
end R1Z.PV_CB3_GammaInjective
