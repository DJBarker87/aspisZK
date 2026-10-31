import NEC_HeaderPredicates
import NEC_LiveHeaderRef.Funs
set_option autoImplicit false
namespace NEC_HeaderBinding3
open Aeneas Aeneas.Std Result NEC_HeaderPredicates

theorem emitted (a : Array U8 48#usize) :
 @Eq (Result Bool) (NEC_LiveHeaderRef.binding3_ok a) (Result.ok (NEC_HeaderPredicates.binding3 a)) := by
 have h40 : Array.index_usize a 40#usize=ok (byte a 40#usize (by decide)) := byte_spec a _ (by decide)
 have h41 : Array.index_usize a 41#usize=ok (byte a 41#usize (by decide)) := byte_spec a _ (by decide)
 have h42 : Array.index_usize a 42#usize=ok (byte a 42#usize (by decide)) := byte_spec a _ (by decide)
 have h43 : Array.index_usize a 43#usize=ok (byte a 43#usize (by decide)) := byte_spec a _ (by decide)
 have h44 : Array.index_usize a 44#usize=ok (byte a 44#usize (by decide)) := byte_spec a _ (by decide)
 have h45 : Array.index_usize a 45#usize=ok (byte a 45#usize (by decide)) := byte_spec a _ (by decide)
 have h46 : Array.index_usize a 46#usize=ok (byte a 46#usize (by decide)) := byte_spec a _ (by decide)
 have h47 : Array.index_usize a 47#usize=ok (byte a 47#usize (by decide)) := byte_spec a _ (by decide)
 unfold NEC_HeaderPredicates.binding3
 simp only [NEC_LiveHeaderRef.binding3_ok,h40,h41,h42,h43,h44,h45,h46,h47,bind_tc_ok]
 repeat' first | rfl | (split <;> simp_all)

#print axioms emitted
end NEC_HeaderBinding3
