import NFQ_STAGE2_IMPORT
set_option autoImplicit false
namespace NFT_Cmr
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
abbrev Canonical := AspisR1.ExtractedMaskTowerAdd.CanonicalCM

def G (x : field.CM31) : Result field.CM31 := do
  let aa ← field.M31.double x.a
  let real ← field.M31.sub aa x.b
  let bb ← field.M31.double x.b
  let imag ← field.M31.add x.a bb
  field.CM31.new real imag

theorem source (x : field.CM31) : G x=state_only_hiding.cm31_mul_r x := by rfl

theorem double_value (x : U32) (canonical : x.val<2147483647) :
    ∃ z, field.M31.double x=ok z ∧ z.val=(x.val+x.val)%2147483647 ∧ z.val<2147483647 := by
  exact AspisR1.ExtractedMaskM31AddSub.current_add_mod x x canonical canonical

theorem sub_value (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    ∃ z, field.M31.sub x y=ok z ∧ z.val=(x.val+2147483647-y.val)%2147483647 ∧ z.val<2147483647 :=
  AspisR1.ExtractedMaskM31AddSub.current_sub_mod x y hx hy

theorem add_value (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    ∃ z, field.M31.add x y=ok z ∧ z.val=(x.val+y.val)%2147483647 ∧ z.val<2147483647 :=
  AspisR1.ExtractedMaskM31AddSub.current_add_mod x y hx hy

#print axioms source
#print axioms double_value
#print axioms sub_value
#print axioms add_value
end NFT_Cmr
