import XRy_Queries
import ExtractedCurrentCM31Mul
import ExtractedCurrentQM31Mul
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRy_Reducer64

theorem reducer (x : U64) :
 XRn_Join_Field.field.M31.reduce_u64 x = AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 x := by
 obtain ⟨z,hz,hv,hc⟩ := AspisR1.LPf_CoreReduction.source x
 obtain ⟨w,hw,hwv,hwc⟩ := AspisR1.ExtractedCurrentReducer.current_wrapper_mod x
 have he : z=w := UScalar.eq_of_val_eq (hv.trans hwv.symm)
 simp only [XRn_Join_Field.field.M31.reduce_u64,XRs_BaseMultiply.same_reducer,hz,bind_tc_ok]
 exact (congrArg Result.ok he).trans hw.symm

theorem add64 (a b : U64) (h : a.val+b.val < 18446744073709551616) :
 a+b = ok (U64.wrapping_add a b) := by
 obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists
   (UScalar.add_spec (x:=a) (y:=b) (by scalar_tac))
 have hw := UScalar.wrapping_add_val_eq a b
 change (U64.wrapping_add a b).val = (a.val+b.val)%18446744073709551616 at hw
 rw [Nat.mod_eq_of_lt h] at hw
 exact hz.trans (congrArg ok (UScalar.eq_of_val_eq (hv.trans hw.symm)))

theorem mul64 (a b : U64) (h : a.val*b.val < 18446744073709551616) :
 a*b = ok (U64.wrapping_mul a b) := by
 obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists
   (UScalar.mul_spec (x:=a) (y:=b) (by scalar_tac))
 have hw := UScalar.wrapping_mul_val_eq a b
 change (U64.wrapping_mul a b).val = (a.val*b.val)%18446744073709551616 at hw
 rw [Nat.mod_eq_of_lt h] at hw
 exact hz.trans (congrArg ok (UScalar.eq_of_val_eq (hv.trans hw.symm)))

#print axioms reducer
#print axioms add64
#print axioms mul64
end XRy_Reducer64
