import NEC_HeaderPredicates
import NEC_LiveHeaderRef.Funs
set_option autoImplicit false
namespace NEC_HeaderBinding1
open Aeneas Aeneas.Std Result NEC_HeaderPredicates

theorem emitted (a : Array U8 48#usize) :
 NEC_LiveHeaderRef.binding1_ok a=ok (NEC_HeaderPredicates.binding1 a) := by
 have h24 : Array.index_usize a 24#usize=ok (byte a 24#usize (by decide)) := byte_spec a _ (by decide)
 have h25 : Array.index_usize a 25#usize=ok (byte a 25#usize (by decide)) := byte_spec a _ (by decide)
 have h26 : Array.index_usize a 26#usize=ok (byte a 26#usize (by decide)) := byte_spec a _ (by decide)
 have h27 : Array.index_usize a 27#usize=ok (byte a 27#usize (by decide)) := byte_spec a _ (by decide)
 have h28 : Array.index_usize a 28#usize=ok (byte a 28#usize (by decide)) := byte_spec a _ (by decide)
 have h29 : Array.index_usize a 29#usize=ok (byte a 29#usize (by decide)) := byte_spec a _ (by decide)
 have h30 : Array.index_usize a 30#usize=ok (byte a 30#usize (by decide)) := byte_spec a _ (by decide)
 have h31 : Array.index_usize a 31#usize=ok (byte a 31#usize (by decide)) := byte_spec a _ (by decide)
 unfold NEC_HeaderPredicates.binding1
 simp only [NEC_LiveHeaderRef.binding1_ok,h24,h25,h26,h27,h28,h29,h30,h31,bind_tc_ok]
 repeat' first | rfl | (split <;> simp_all)

#print axioms emitted
end NEC_HeaderBinding1
