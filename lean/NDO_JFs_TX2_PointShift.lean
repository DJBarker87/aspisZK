import NDO_JFs_TX2_PointCall
set_option autoImplicit false
namespace AspisR1.JFs_TX2_PointShift
open Aeneas Aeneas.Std Result

theorem source (u hi : Usize) (value : hi.val=u.val/512) : u >>> 9#i32=ok hi := by
  have hn0 : 0≤(9#i32).val := by decide
  have hn1 : (9#i32).val<UScalarTy.Usize.numBits := by
    cases System.Platform.numBits_eq <;> norm_num [UScalarTy.Usize_numBits_eq, *]
  obtain ⟨out,run,⟨v,_⟩⟩ := WP.spec_imp_exists (UScalar.ShiftRight_IScalar_spec u (9#i32) hn0 hn1)
  have decoded : out.val=u.val/512 := by
    rw [v]
    simp [IScalar.toNat,Nat.shiftRight_eq_div_pow]
  have same : out=hi := UScalar.eq_of_val_eq (decoded.trans value.symm)
  exact same ▸ run

#print axioms source
end AspisR1.JFs_TX2_PointShift
