import NEC_HeaderPredicates
import NEC_LiveHeaderRef.Funs
set_option autoImplicit false
namespace NEC_HeaderMagic
open Aeneas Aeneas.Std Result NEC_HeaderPredicates

theorem emitted (a : Array U8 48#usize) :
 NEC_LiveHeaderRef.magic_ok a=ok (NEC_HeaderPredicates.magic a) := by
 have h0 : Array.index_usize a 0#usize=ok (byte a 0#usize (by decide)) := byte_spec a _ (by decide)
 have h1 : Array.index_usize a 1#usize=ok (byte a 1#usize (by decide)) := byte_spec a _ (by decide)
 have h2 : Array.index_usize a 2#usize=ok (byte a 2#usize (by decide)) := byte_spec a _ (by decide)
 have h3 : Array.index_usize a 3#usize=ok (byte a 3#usize (by decide)) := byte_spec a _ (by decide)
 have h4 : Array.index_usize a 4#usize=ok (byte a 4#usize (by decide)) := byte_spec a _ (by decide)
 have h5 : Array.index_usize a 5#usize=ok (byte a 5#usize (by decide)) := byte_spec a _ (by decide)
 have h6 : Array.index_usize a 6#usize=ok (byte a 6#usize (by decide)) := byte_spec a _ (by decide)
 have h7 : Array.index_usize a 7#usize=ok (byte a 7#usize (by decide)) := byte_spec a _ (by decide)
 unfold NEC_HeaderPredicates.magic
 simp only [NEC_LiveHeaderRef.magic_ok,h0,h1,h2,h3,h4,h5,h6,h7,bind_tc_ok]
 repeat' first | rfl | (split <;> simp_all)

#print axioms emitted
end NEC_HeaderMagic
