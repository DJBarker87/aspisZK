import NGO_QRef.Funs
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
    step*
    simp_all [segment,Array.make,core.num.U32.from_le_bytes,
      UScalar.wrapping_shl,UScalar.or,core.convert.num.FromU32U8.from]
  obtain ⟨out,run,eq⟩ := WP.spec_imp_exists spec
  exact run.trans (congrArg ok eq)
#print axioms word
end NGO_WordLaw
