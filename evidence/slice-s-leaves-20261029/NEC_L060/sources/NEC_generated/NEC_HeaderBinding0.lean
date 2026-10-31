import NEC_HeaderPredicates
import NEC_LiveHeaderRef.Funs
set_option autoImplicit false
namespace NEC_HeaderBinding0
open Aeneas Aeneas.Std Result NEC_HeaderPredicates

theorem emitted (a : Array U8 48#usize) :
 NEC_LiveHeaderRef.binding0_ok a=ok (NEC_HeaderPredicates.binding0 a) := by
 have h16 : Array.index_usize a 16#usize=ok (byte a 16#usize (by decide)) := byte_spec a _ (by decide)
 have h17 : Array.index_usize a 17#usize=ok (byte a 17#usize (by decide)) := byte_spec a _ (by decide)
 have h18 : Array.index_usize a 18#usize=ok (byte a 18#usize (by decide)) := byte_spec a _ (by decide)
 have h19 : Array.index_usize a 19#usize=ok (byte a 19#usize (by decide)) := byte_spec a _ (by decide)
 have h20 : Array.index_usize a 20#usize=ok (byte a 20#usize (by decide)) := byte_spec a _ (by decide)
 have h21 : Array.index_usize a 21#usize=ok (byte a 21#usize (by decide)) := byte_spec a _ (by decide)
 have h22 : Array.index_usize a 22#usize=ok (byte a 22#usize (by decide)) := byte_spec a _ (by decide)
 have h23 : Array.index_usize a 23#usize=ok (byte a 23#usize (by decide)) := byte_spec a _ (by decide)
 unfold NEC_HeaderPredicates.binding0
 simp only [NEC_LiveHeaderRef.binding0_ok,h16,h17,h18,h19,h20,h21,h22,h23,bind_tc_ok]
 repeat' first | rfl | (split <;> simp_all)

#print axioms emitted
end NEC_HeaderBinding0
