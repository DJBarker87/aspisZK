import R1Z.PV_B2_Decode
set_option autoImplicit false
noncomputable section
namespace PV_B2_DecodeResult
open Aeneas Aeneas.Std Result PV_B2_SamplerCarrier

theorem unwrap (o : Option Raw) :
    mapResult toNative (core.option.Option.unwrap o) =
      core.option.Option.unwrap (Option.map toNative o) := by cases o <;> rfl

/-- The checked limb decoder preserves panic and divergence as well as values. -/
theorem source (a : Array U32 8#usize) :
    mapResult toNative (PV_B2_249.host_sampler.decode8 a) =
      PV_B2_Sampler.host_sampler.decode8 a := by
  unfold PV_B2_249.host_sampler.decode8 PV_B2_Sampler.host_sampler.decode8
  rw [map_bind]
  have hc := PV_B2_Decode.constructor_transport a
  cases h : PV_B2_249.aspis_core.field.wide_exact.WideExact.from_limbs a with
  | ok o =>
    rw [h] at hc
    simp only [mapResult] at hc
    rw [←hc]
    simp only [bind_tc_ok]
    exact unwrap o
  | fail e =>
    rw [h] at hc
    simp only [mapResult] at hc
    rw [←hc]
    rfl
  | div =>
    rw [h] at hc
    simp only [mapResult] at hc
    rw [←hc]
    rfl
#print axioms unwrap
#print axioms source
end PV_B2_DecodeResult
