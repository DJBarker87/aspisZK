import NGO_BitPack
import NGD_QDecodeLaw
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace NGO_WordLaw
/-- Four input byte positions, in source order. -/
def segment (arr : Array U8 16#usize) (i : Usize) (bound : i.val≤12) : Array U8 4#usize :=
  Array.make 4#usize [
    arr.val[i.val]'(by rw [arr.property];change i.val<16;omega),
    arr.val[i.val+1]'(by rw [arr.property];change i.val+1<16;omega),
    arr.val[i.val+2]'(by rw [arr.property];change i.val+2<16;omega),
    arr.val[i.val+3]'(by rw [arr.property];change i.val+3<16;omega)]
theorem word (arr : Array U8 16#usize) (i : Usize) (bound : i.val≤12) :
    NGO_QRef.NGO_decode_le.word (Array.to_slice arr) i =
      ok (core.num.U32.from_le_bytes (segment arr i bound)) := by
  have spec : NGO_QRef.NGO_decode_le.word (Array.to_slice arr) i ⦃ out =>
      out=core.num.U32.from_le_bytes (segment arr i bound) ⦄ := by
    unfold NGO_QRef.NGO_decode_le.word
    simp only [lift,bind_tc_ok]
    have w1 : (Usize.wrapping_add i 1#usize).val=i.val+1 := by
      rw [Usize.wrapping_add_val_eq];apply Nat.mod_eq_of_lt;rw [UScalar.size_def];scalar_tac
    have w2 : (Usize.wrapping_add i 2#usize).val=i.val+2 := by
      rw [Usize.wrapping_add_val_eq];apply Nat.mod_eq_of_lt;rw [UScalar.size_def];scalar_tac
    have w3 : (Usize.wrapping_add i 3#usize).val=i.val+3 := by
      rw [Usize.wrapping_add_val_eq];apply Nat.mod_eq_of_lt;rw [UScalar.size_def];scalar_tac
    step*
    all_goals simp_all [w1,w2,w3,Array.to_slice] 
    all_goals simpa only [segment,Array.make,i1_post,i4_post,i9_post,i14_post] using NGO_BitPack.pack i1 i4 i9 i14
  obtain ⟨out,run,eq⟩ := WP.spec_imp_exists spec
  exact run.trans (congrArg ok eq)
#print axioms word
end NGO_WordLaw
