import R1Z.ProverRwFullTypes
import R1Z.PV_B2_C_GammaSource
set_option autoImplicit false
namespace PV_B2_C_NativeGammaCarrier
open Aeneas Aeneas.Std Result
open AspisR1 AspisR1.SamplerNatModel AspisR1.SamplerMachineBounds
open AspisR1.SamplerAddDigits AspisR1.SourceSamplerByteRank PV_B2_C_GammaNumeric
abbrev Raw := PV_B2_C_249.aspis_core.field.wide_exact.WideExact
abbrev Native := ProverRwFull.aspis_core.field.wide_exact.WideExact
def toNative (v : Raw) : Native :=
  ⟨⟨⟨v.c0.c0.a,v.c0.c0.b⟩,⟨v.c0.c1.a,v.c0.c1.b⟩⟩,
   ⟨⟨v.c1.c0.a,v.c1.c0.b⟩,⟨v.c1.c1.a,v.c1.c1.b⟩⟩⟩
def fromNative (v : Native) : Raw :=
  ⟨⟨⟨v.c0.c0.a,v.c0.c0.b⟩,⟨v.c0.c1.a,v.c0.c1.b⟩⟩,
   ⟨⟨v.c1.c0.a,v.c1.c0.b⟩,⟨v.c1.c1.a,v.c1.c1.b⟩⟩⟩
def mapResult {α β : Type} (f : α → β) : Result α → Result β
  | .ok v => .ok (f v)
  | .fail e => .fail e
  | .div => .div
@[simp] theorem roundtrip (v : Native) : toNative (fromNative v) = v := by cases v; rfl
@[simp] theorem roundtrip_raw (v : Raw) : fromNative (toNative v) = v := by cases v; rfl
theorem map_injective (x y : Result Raw) :
    mapResult toNative x = mapResult toNative y ↔ x = y := by
  constructor
  · intro h
    have h' := congrArg (mapResult fromNative) h
    cases x <;> cases y <;> simpa only [mapResult,roundtrip_raw] using h'
  · exact congrArg _
/-- Carrier transport of the complete gamma source Result. This does not identify
an original shipped function or discharge V256. -/
theorem gamma (b : Bytes32) :
    ∃ ds : PV_B2_C_GammaNumeric.Digits,
      mapResult toNative (PV_B2_C_249.host_sampler.gamma_sample b) =
        ok (toNative (PV_B2_C_ArrayDigits.raw ds)) ∧
      PV_B2_C_GammaNumeric.Canonical ds ∧
      digitsValue P
        (PV_B2_C_GammaNumeric.values ds) =
          rank b % (P^8-1)+1 := by
  obtain ⟨ds,he,hc,hr,_,_⟩ := PV_B2_C_GammaSource.op249_source b
  exact ⟨ds,by rw [he];rfl,hc,hr⟩
#print axioms roundtrip
#print axioms roundtrip_raw
#print axioms map_injective
#print axioms gamma
end PV_B2_C_NativeGammaCarrier
