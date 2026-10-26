import FIo_M31Values
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_ReduceValues
open Aeneas Aeneas.Std Result

theorem checked_probe (x : U64) :
    AspisR1CurrentWide.field.reduce_u64 x=AspisR1Qm31ArithmeticProbe.field.reduce_u64 x := by
  simp only [AspisR1CurrentWide.field.reduce_u64,AspisR1Qm31ArithmeticProbe.field.reduce_u64,
    AspisR1CurrentWide.field.P,AspisR1Qm31ArithmeticProbe.field.P]
  rfl

theorem value (x : U64) (z : U32)
    (run : FIo_Native.aspis_core.field.reduce_u64 x=ok z) :
    z.val=x.val%2147483647 ∧ z.val<2147483647 := by
  have actual := (FIo_ReduceBridge.same x).symm.trans run
  rw [checked_probe] at actual
  obtain ⟨out,ho,value,canonical⟩ := ExtractedCurrentReducer.current_reduce_mod x
  have same : out=z := Result.ok.inj (ho.symm.trans actual)
  exact same ▸ ⟨value,canonical⟩

theorem m31_value (x : U64) (z : U32)
    (run : FIo_Native.aspis_core.field.M31.reduce_u64 x=ok z) :
    z.val=x.val%2147483647 ∧ z.val<2147483647 := by
  exact value x z run

#print axioms checked_probe
#print axioms value
#print axioms m31_value
end AspisR1.FIo_ReduceValues
end
