import NMT_345ZeroRange
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result ControlFlow
open _root_.AdapterRw
open NFQ_ZeroReference (terminal)
/-- Complete finite-loop relation, including rejection and divergence carriers. -/
theorem loop_reference (bytes : Slice U8) (n : Nat) (i : Usize) (left : i.val+n=bytes.val.length) :
    (do let b ← NFQ_ScanReference.zero_ref_loop bytes i true;ok (terminal b)) =
      r1_pool_adapter.owned.require_zero_loop bytes i := by
  induction n generalizing i with
  | zero =>
    have outside : ¬i<Slice.len bytes := by change ¬i.val<bytes.val.length;omega
    conv_lhs =>
      unfold NFQ_ScanReference.zero_ref_loop
      rw [Aeneas.Std.loop.eq_def]
      simp only [NFQ_ScanReference.zero_ref_loop.body,if_neg outside,bind_tc_ok]
    conv_rhs =>
      unfold r1_pool_adapter.owned.require_zero_loop
      rw [Aeneas.Std.loop.eq_def]
      simp only [r1_pool_adapter.owned.require_zero_loop.body,if_neg outside]
    rfl
  | succ n ih =>
    have inside : i.val<bytes.val.length := by omega
    let byte : U8 := bytes.val[i.val]'inside
    have selected : bytes.val[i.val]?=some byte := by
      simp only [byte,List.getElem?_eq_getElem inside]
    have call := NFQ_ZeroPrimitives.index_read bytes i inside byte selected
    have inc : (Usize.wrapping_add i 1#usize).val=i.val+1 :=
      zero_increment bytes i inside
    by_cases hz : byte=0#u8
    · have rest := ih (Usize.wrapping_add i 1#usize) (by rw [inc];omega)
      conv_lhs =>
        unfold NFQ_ScanReference.zero_ref_loop
        rw [Aeneas.Std.loop.eq_def]
        simp only [NFQ_ScanReference.zero_ref_loop.body,
          if_pos (show i<Slice.len bytes from inside),if_true,call,hz,lift,bind_tc_ok]
      conv_rhs =>
        unfold r1_pool_adapter.owned.require_zero_loop
        rw [Aeneas.Std.loop.eq_def]
        simp only [r1_pool_adapter.owned.require_zero_loop.body,
          if_pos (show i<Slice.len bytes from inside),call,hz,
          show (0#u8 != 0#u8)=false from rfl,Bool.false_eq_true,if_false,lift,bind_tc_ok]
      simpa only [NFQ_ScanReference.zero_ref_loop,
        r1_pool_adapter.owned.require_zero_loop,NFQ_ScanReference.zero_ref_loop.body,
        r1_pool_adapter.owned.require_zero_loop.body,lift,bind_tc_ok,decide_true] using rest
    · rw [NFQ_ZeroGateModel.reject_at bytes i byte inside selected hz]
      conv_lhs =>
        unfold NFQ_ScanReference.zero_ref_loop
        rw [Aeneas.Std.loop.eq_def]
        simp only [NFQ_ScanReference.zero_ref_loop.body,
          if_pos (show i<Slice.len bytes from inside),if_true,call,hz,decide_false,lift,bind_tc_ok]
      change (do let b ← NFQ_ScanReference.zero_ref_loop bytes (Usize.wrapping_add i 1#usize) false
                 ok (terminal b))=ok _
      rw [NFQ_ZeroReference.false_loop]
      rfl

#print axioms loop_reference
end NMT_345
