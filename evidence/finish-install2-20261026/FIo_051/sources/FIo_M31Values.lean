import FIo_M31MulBridge
import FIo_M31SubBridge
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_M31Values
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof

theorem add (x y z : U32) (hx : x.val<2147483647) (hy : y.val<2147483647)
    (run : FIo_Native.aspis_core.field.M31.add x y=ok z) :
    z.val<2147483647 ∧ decodeM z=decodeM x+decodeM y := by
  have hc : AspisR1CurrentWide.field.M31.add x y=ok z := by
    rw [←FIo_M31Bridge.add x y hx hy]; exact run
  have value := m31_add_exact x y z hc
  rw [m31_add_same] at hc
  obtain ⟨out,ho,_,canonical⟩ := ExtractedCurrentM31AddSub.current_add_mod x y hx hy
  have same : out=z := Result.ok.inj (ho.symm.trans hc)
  exact ⟨same ▸ canonical,value⟩

theorem sub (x y z : U32) (hx : x.val<2147483647) (hy : y.val<2147483647)
    (run : FIo_Native.aspis_core.field.M31.sub x y=ok z) :
    z.val<2147483647 ∧ decodeM z=decodeM x-decodeM y := by
  have hc : AspisR1CurrentWide.field.M31.sub x y=ok z := by
    rw [←FIo_M31SubBridge.sub x y hx hy]; exact run
  have value := m31_sub_exact x y z hc
  rw [m31_sub_same] at hc
  exact ⟨R17CurrentDomainCanonical.sub_success_canonical x y z hx hy hc,value⟩

theorem mul (x y z : U32) (run : FIo_Native.aspis_core.field.M31.mul x y=ok z) :
    z.val<2147483647 ∧ decodeM z=decodeM x*decodeM y := by
  have hc : AspisR1CurrentWide.field.M31.mul x y=ok z := by
    rw [←FIo_M31MulBridge.same x y]; exact run
  rw [m31_mul_same] at hc
  exact ⟨R17CurrentDomainCanonical.mul_success_canonical x y z hc,
    R17CurrentM31Semantics.current_mul_decode x y z hc⟩

#print axioms add
#print axioms sub
#print axioms mul
end AspisR1.FIo_M31Values
end
