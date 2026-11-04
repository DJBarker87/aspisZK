import NFQ_ZeroReference
set_option autoImplicit false
namespace NFQ_ZeroStep
open Aeneas Aeneas.Std Result ControlFlow
open _root_.AdapterRw

theorem zero_step (bytes : Slice U8) (i : Usize) (inside : i.val<bytes.val.length)
 (selected : bytes.val[i.val]?=some 0#u8) :
 r1_pool_adapter.owned.require_zero_loop.body bytes i=
   ok (cont (Usize.wrapping_add i 1#usize)) := by
 have call := NFQ_ZeroPrimitives.index_read bytes i inside 0#u8 selected
 simp only [r1_pool_adapter.owned.require_zero_loop.body,
   if_pos (show i<Slice.len bytes from inside),call,bind_tc_ok,
   show (0#u8 != 0#u8)=false from rfl,Bool.false_eq_true,if_false,lift]

theorem reject_step (bytes : Slice U8) (i : Usize) (b : U8)
 (inside : i.val<bytes.val.length) (selected : bytes.val[i.val]?=some b) (nz : b≠0#u8) :
 r1_pool_adapter.owned.require_zero_loop.body bytes i=
   ok (done (some (.Err .AccountAlreadyInitialized))) := by
 have call := NFQ_ZeroPrimitives.index_read bytes i inside b selected
 simp only [r1_pool_adapter.owned.require_zero_loop.body,
   if_pos (show i<Slice.len bytes from inside),call,bind_tc_ok]
 simp [nz]
#print axioms zero_step
#print axioms reject_step
end NFQ_ZeroStep
