import NEV_DotCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFC_ScalarAdd
open Aeneas Aeneas.Std Result
/-- Natural scalar domain for the actual wrapping add; no multiplication. -/
theorem total (a b : U32) (ha : a.val<2147483647) (hb : b.val<2147483647) :
    ∃ c,FIo_Native.aspis_core.field.M31.add a b=ok c ∧
      c.val<2147483647 ∧ c.val=(a.val+b.val)%2147483647 := by
  let sum:=U32.wrapping_add a b
  have sumVal : sum.val=a.val+b.val := by
    dsimp only [sum]
    rw [UScalar.wrapping_add_val_eq]
    change (a.val+b.val)%4294967296=a.val+b.val
    exact Nat.mod_eq_of_lt (by omega)
  unfold FIo_Native.aspis_core.field.M31.add
  simp only [lift,bind_tc_ok,FIo_Native.aspis_core.field.P]
  change ∃ c,(if sum≥2147483647#u32 then ok (U32.wrapping_sub sum 2147483647#u32)
    else ok sum)=ok c ∧ _
  split
  · rename_i above
    have lower : 2147483647≤sum.val := by scalar_tac
    refine ⟨_,rfl,?_,?_⟩
    all_goals
      rw [UScalar.wrapping_sub_val_eq]
      norm_num [UScalar.size,UScalarTy.numBits,U32.size,U32.numBits]
      omega
  · rename_i below
    have upper : sum.val<2147483647 := by scalar_tac
    refine ⟨sum,rfl,upper,?_⟩
    rw [sumVal,Nat.mod_eq_of_lt (by omega)]
#print axioms total
end AspisR1.NFC_ScalarAdd
end
