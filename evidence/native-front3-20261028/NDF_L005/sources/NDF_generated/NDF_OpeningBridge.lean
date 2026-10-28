import NDF_Reference.Funs
import Port4B_Opening
set_option autoImplicit false
namespace NDF_OpeningBridge
open Aeneas Aeneas.Std Result

theorem reference (proof : Slice U8) (i : Usize) (bound : i.val < 22) :
    NDF_Reference.opening_ref proof i = AspisR1.Port4B_Opening.opening proof i := by
  have hm : i.val * 832 < UScalar.size .Usize := by
    have cap : 57607 < UScalar.size .Usize := by rw [UScalar.size_def]; scalar_tac
    omega
  have mul : (i * 832#usize : Result Usize) = ok (Usize.wrapping_mul i 832#usize) := by
    scalar_tac
  have mv : (Usize.wrapping_mul i 832#usize).val = i.val*832 := by
    rw [Usize.wrapping_mul_val_eq]
    exact Nat.mod_eq_of_lt hm
  have add : (10055#usize + Usize.wrapping_mul i 832#usize : Result Usize) =
      ok (Usize.wrapping_add 10055#usize (Usize.wrapping_mul i 832#usize)) := by
    scalar_tac
  have sv : (Usize.wrapping_add 10055#usize (Usize.wrapping_mul i 832#usize)).val = 10055+i.val*832 := by
    rw [Usize.wrapping_add_val_eq,mv]
    apply Nat.mod_eq_of_lt
    rw [UScalar.size_def]
    scalar_tac
  have finish : ((Usize.wrapping_add 10055#usize (Usize.wrapping_mul i 832#usize)) + 832#usize : Result Usize) =
      ok (Usize.wrapping_add (Usize.wrapping_add 10055#usize (Usize.wrapping_mul i 832#usize)) 832#usize) := by
    scalar_tac
  simp only [NDF_Reference.opening_ref,AspisR1.Port4B_Opening.opening,mul,add,finish,lift,bind_tc_ok]

#print axioms reference
end NDF_OpeningBridge
