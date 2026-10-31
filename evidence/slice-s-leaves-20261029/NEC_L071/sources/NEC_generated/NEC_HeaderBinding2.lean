import NEC_HeaderGuards
import NEC_LiveHeaderRef.Funs
set_option autoImplicit false
namespace NEC_HeaderBinding2
open Aeneas Aeneas.Std Result NEC_HeaderPredicates

theorem emitted (a : Array U8 48#usize) :
 NEC_LiveHeaderRef.binding2_ok a=ok (NEC_HeaderPredicates.binding2 a) := by
 have h32 : Array.index_usize a 32#usize=ok (byte a 32#usize (by decide)) := byte_spec a _ (by decide)
 have h33 : Array.index_usize a 33#usize=ok (byte a 33#usize (by decide)) := byte_spec a _ (by decide)
 have h34 : Array.index_usize a 34#usize=ok (byte a 34#usize (by decide)) := byte_spec a _ (by decide)
 have h35 : Array.index_usize a 35#usize=ok (byte a 35#usize (by decide)) := byte_spec a _ (by decide)
 have h36 : Array.index_usize a 36#usize=ok (byte a 36#usize (by decide)) := byte_spec a _ (by decide)
 have h37 : Array.index_usize a 37#usize=ok (byte a 37#usize (by decide)) := byte_spec a _ (by decide)
 have h38 : Array.index_usize a 38#usize=ok (byte a 38#usize (by decide)) := byte_spec a _ (by decide)
 have h39 : Array.index_usize a 39#usize=ok (byte a 39#usize (by decide)) := byte_spec a _ (by decide)
 unfold NEC_HeaderPredicates.binding2
 simp only [NEC_LiveHeaderRef.binding2_ok,h32,h33,h34,h35,h36,h37,h38,h39,bind_tc_ok,NEC_HeaderGuards.guarded]

#print axioms emitted
end NEC_HeaderBinding2
