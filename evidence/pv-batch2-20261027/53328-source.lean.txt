import R1Z.PV_B2_SamplerHelpers
import R1Z.PV_B2_DecodeResult
set_option autoImplicit false
noncomputable section
namespace PV_B2_GammaCarrier
open Aeneas Aeneas.Std Result PV_B2_SamplerCarrier
abbrev Digits := Array U32 8#usize

def rest (wrapped : Bool) (digits : Digits) : Result Digits :=
  if wrapped then do
    let (_,out) ← PV_B2_Sampler.host_sampler.add_small_base_p digits 1#u32
    ok out
  else ok digits

theorem tail_source (r : Result Digits) :
    mapResult toNative (do let d ← r; PV_B2_249.host_sampler.decode8 d) =
      (do let d ← r; PV_B2_Sampler.host_sampler.decode8 d) := by
  rw [map_bind]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro d _
  exact PV_B2_DecodeResult.source d

theorem after_low (digits : Digits) (q : U32) :
    mapResult toNative (do
      let i ← lift (U32.wrapping_add q 1#u32)
      let (wrapped,digits1) ← PV_B2_Sampler.host_sampler.add_small_base_p digits i
      let digits2 ← rest wrapped digits1
      PV_B2_249.host_sampler.decode8 digits2) =
    (do
      let i ← lift (U32.wrapping_add q 1#u32)
      let (wrapped,digits1) ← PV_B2_Sampler.host_sampler.add_small_base_p digits i
      let digits2 ← rest wrapped digits1
      PV_B2_Sampler.host_sampler.decode8 digits2) := by
  simp only [lift,bind_tc_ok,map_bind]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨wrapped,digits1⟩ _
  exact tail_source (rest wrapped digits1)

/-- Full Result equality between the unmodified raw gamma emission and its
native-carrier presentation, for every byte block. This is not copy/original
native equivalence or the gamma rank law. -/
theorem source (block : Array U8 32#usize) :
    mapResult toNative (PV_B2_249.host_sampler.gamma_sample block) =
      PV_B2_Sampler.host_sampler.gamma_sample block := by
  unfold PV_B2_249.host_sampler.gamma_sample PV_B2_Sampler.host_sampler.gamma_sample
  simp only [PV_B2_SamplerHelpers.low,PV_B2_SamplerHelpers.small,map_bind]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨digits,q⟩ _
  exact after_low digits q
#print axioms tail_source
#print axioms after_low
#print axioms source
end PV_B2_GammaCarrier
