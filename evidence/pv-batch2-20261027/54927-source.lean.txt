import R1Z.PV_B2_SamplerCarrier
set_option autoImplicit false
noncomputable section
namespace PV_B2_Decode
open Aeneas Aeneas.Std Result PV_B2_SamplerCarrier

theorem constructor_transport (a : Array U32 8#usize) :
    mapResult (Option.map toNative)
      (PV_B2_249.aspis_core.field.wide_exact.WideExact.from_limbs a) =
      PV_B2_Sampler.aspis_core.field.wide_exact.WideExact.from_limbs a := by
  unfold PV_B2_249.aspis_core.field.wide_exact.WideExact.from_limbs
    PV_B2_Sampler.aspis_core.field.wide_exact.WideExact.from_limbs
  simp only [PV_B2_249.aspis_core.field.P,PV_B2_Sampler.aspis_core.field.P]
  rw [map_bind]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro x0 _
  by_cases h0 : x0 >= 2147483647#u32
  · simp only [if_pos h0,mapResult,Option.map]
  · simp only [if_neg h0]
    rw [map_bind]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro x1 _
    by_cases h1 : x1 >= 2147483647#u32
    · simp only [if_pos h1,mapResult,Option.map]
    · simp only [if_neg h1]
      rw [map_bind]
      apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro x2 _
      by_cases h2 : x2 >= 2147483647#u32
      · simp only [if_pos h2,mapResult,Option.map]
      · simp only [if_neg h2]
        rw [map_bind]
        apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro x3 _
        by_cases h3 : x3 >= 2147483647#u32
        · simp only [if_pos h3,mapResult,Option.map]
        · simp only [if_neg h3]
          rw [map_bind]
          apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
          intro x4 _
          by_cases h4 : x4 >= 2147483647#u32
          · simp only [if_pos h4,mapResult,Option.map]
          · simp only [if_neg h4]
            rw [map_bind]
            apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
            intro x5 _
            by_cases h5 : x5 >= 2147483647#u32
            · simp only [if_pos h5,mapResult,Option.map]
            · simp only [if_neg h5]
              rw [map_bind]
              apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
              intro x6 _
              by_cases h6 : x6 >= 2147483647#u32
              · simp only [if_pos h6,mapResult,Option.map]
              · simp only [if_neg h6]
                rw [map_bind]
                apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
                intro x7 _
                by_cases h7 : x7 >= 2147483647#u32
                · simp only [if_pos h7,mapResult,Option.map]
                · simp only [if_neg h7]
                  rfl

#print axioms constructor_transport
end PV_B2_Decode
