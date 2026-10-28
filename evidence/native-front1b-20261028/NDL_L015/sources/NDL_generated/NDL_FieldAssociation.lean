import NCJ_FieldTotal
import NDL_Reference.Funs
import NDD_ScalarCanon
set_option autoImplicit false
noncomputable section
namespace NDL_FieldAssociation
open Aeneas Aeneas.Std Result

theorem checked_add (x y : Usize) (bound : x.val+y.val < 2^Usize.numBits) :
    x+y = ok (Usize.wrapping_add x y) := by
  obtain ⟨z,hz,hv⟩ := AspisR1.ExtractedMaskReducerOps.tryMk_success (ty:=.Usize)
    (x.val+y.val) bound
  have hval : z.val = (Usize.wrapping_add x y).val := by
    rw [hv,Usize.wrapping_add_val_eq,Nat.mod_eq_of_lt bound]
  have he := UScalar.eq_of_val_eq hval
  simpa only [he] using hz

theorem checked_mul (x y : Usize) (bound : x.val*y.val < 2^Usize.numBits) :
    x*y = ok (Usize.wrapping_mul x y) := by
  obtain ⟨z,hz,hv⟩ := AspisR1.ExtractedMaskReducerOps.tryMk_success (ty:=.Usize)
    (x.val*y.val) bound
  have hval : z.val = (Usize.wrapping_mul x y).val := by
    rw [hv,Usize.wrapping_mul_val_eq,Nat.mod_eq_of_lt bound]
  have he := UScalar.eq_of_val_eq hval
  simpa only [he] using hz

/-- The extracted safe reference's checked offsets agree with the cohort's
wrapping offsets whenever the actual selected slice is source-valid. -/
theorem offsets (i : Usize) (fits : 32*(i.val+1)<UScalar.size .Usize) :
    NDL_Reference.range_ref i = ok
      (Usize.wrapping_mul i 32#usize,
       Usize.wrapping_mul (Usize.wrapping_add i 1#usize) 32#usize) := by
  have fit : 32*(i.val+1)<2^Usize.numBits := by simpa [UScalar.size] using fits
  have v1 : (1#usize).val=1 := by scalar_tac
  have v32 : (32#usize).val=32 := by scalar_tac
  have addbound : i.val+(1#usize).val<2^Usize.numBits := by omega
  have mulbound : i.val*(32#usize).val<2^Usize.numBits := by rw [v32];omega
  have next : (Usize.wrapping_add i 1#usize).val=i.val+1 := by
    rw [Usize.wrapping_add_val_eq,v1,Nat.mod_eq_of_lt (by omega)]
  simp only [NDL_Reference.range_ref,checked_add i _ addbound,
    checked_mul i _ mulbound,bind_tc_ok]
  rw [checked_mul _ _ (by rw [next,v32];omega)]
  rfl

/-- No successful decoder observation is assumed. Canonicality of the SAME
selected bytes constructs the actual cohort result. -/
theorem selected (bytes : Slice U8) (i : Usize)
    (bound : 32*(i.val+1)≤bytes.val.length)
    (canonical : ∀ part : Array U8 32#usize,
      part.val=(bytes.val.drop (32*i.val)).take 32 → NCJ_FieldTotal.Canonical part) :
    ∃ part : Array U8 32#usize,
      part.val=(bytes.val.drop (32*i.val)).take 32 ∧
      FIo_Native.weights.field bytes i=ok (NCJ_FieldTotal.decode part) ∧
      AspisR1.LPi_FieldValues.canonE (NCJ_FieldTotal.decode part) :=
  NCJ_FieldTotal.source bytes i bound canonical

#print axioms checked_add
#print axioms checked_mul
#print axioms offsets
#print axioms selected
end NDL_FieldAssociation
end
