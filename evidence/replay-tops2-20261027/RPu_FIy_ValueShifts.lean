import RPu_FIw_ScalarArithmetic
set_option autoImplicit false
namespace AspisR1.FIy_ValueShifts
open Aeneas Aeneas.Std Result WP

theorem value (distance : I32) (out : U32) (h0 : 0≤distance.val) (h1 : distance.val<32)
    (success : 1#u32 <<< distance=ok out) : out.val=(1 <<< distance.toNat)%UScalar.size UScalarTy.U32 := by
  obtain ⟨out',hr,hv⟩ := WP.spec_imp_exists (UScalar.ShiftLeft_IScalar_spec (1#u32) distance
    (UScalar.size UScalarTy.U32) h0 h1 rfl)
  have eq := Result.ok.inj (hr.symm.trans success)
  subst out'
  exact hv.1

theorem ten (out : U32) (success : 1#u32 <<< 10#i32=ok out) : out.val=1024 := by
  have v := value 10#i32 out (by decide) (by decide) success
  norm_num [UScalar.size,U32.size,U32.numBits,UScalarTy.U32_numBits_eq,IScalar.toNat] at v
  exact v

theorem twenty (out : U32) (success : 1#u32 <<< 20#i32=ok out) : out.val=1048576 := by
  have v := value 20#i32 out (by decide) (by decide) success
  norm_num [UScalar.size,U32.size,U32.numBits,UScalarTy.U32_numBits_eq,IScalar.toNat] at v
  exact v
#print axioms value
#print axioms ten
#print axioms twenty
end AspisR1.FIy_ValueShifts
