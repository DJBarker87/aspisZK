import R1Z.PV_B2_SamplerCarrier
import R1Z.PV_CB3_ArrayEight
set_option autoImplicit false
noncomputable section
namespace PV_B2_Decode
open Aeneas Aeneas.Std Result PV_B2_SamplerCarrier

theorem constructor_transport (a : Array U32 8#usize) :
    mapResult (Option.map toNative)
      (PV_B2_249.aspis_core.field.wide_exact.WideExact.from_limbs a) =
      PV_B2_Sampler.aspis_core.field.wide_exact.WideExact.from_limbs a := by
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,h⟩ := R1Z.PV_CB3_ArrayEight.view a
  subst a
  simp only [PV_B2_249.aspis_core.field.wide_exact.WideExact.from_limbs,
    PV_B2_Sampler.aspis_core.field.wide_exact.WideExact.from_limbs,
    PV_B2_249.aspis_core.field.P,PV_B2_Sampler.aspis_core.field.P]
  simp only [R1Z.PV_CB3_StagedTotal.read_eq]
  simp only [Array.make,List.getElem_cons_zero,List.getElem_cons_succ,bind_tc_ok]
  split_ifs <;> simp_all [mapResult,Option.map,toNative]

#print axioms constructor_transport
end PV_B2_Decode
