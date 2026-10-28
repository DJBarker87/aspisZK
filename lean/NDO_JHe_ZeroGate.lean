import AdapterRwModel
import NDO_JFt_Index
import Port3_Wrapping
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_ZeroGate
open Aeneas Aeneas.Std Result ControlFlow
open _root_.AdapterRw

theorem loop_zero (bytes : Slice U8) (zero : ∀ b ∈ bytes.val,b=0#u8)
    (bound : bytes.val.length≤4096) (n : Nat) (i : Usize) (left : i.val+n=bytes.val.length) :
    r1_pool_adapter.owned.require_zero_loop bytes i=ok none := by
  induction n generalizing i with
  | zero =>
    unfold r1_pool_adapter.owned.require_zero_loop
    rw [Aeneas.Std.loop.eq_def]
    simp only [r1_pool_adapter.owned.require_zero_loop.body,
      if_neg (show ¬i<Slice.len bytes from by change ¬i.val<bytes.val.length;omega),bind_tc_ok]
  | succ n ih =>
    have inside : i.val<bytes.val.length := by omega
    have read : Slice.index_usize bytes i=ok 0#u8 := by
      apply JFt_Index.source bytes i inside 0#u8
      rw [List.getElem?_eq_getElem inside,zero _ (List.getElem_mem _)]
    have inc : (Usize.wrapping_add i 1#usize).val=i.val+1 :=
      Port3_Wrapping.wrap_add_value i 1#usize (by change i.val+1≤4096;omega)
    have rest := ih (Usize.wrapping_add i 1#usize) (by rw [inc];omega)
    unfold r1_pool_adapter.owned.require_zero_loop
    rw [Aeneas.Std.loop.eq_def]
    simp only [r1_pool_adapter.owned.require_zero_loop.body,
      if_pos (show i<Slice.len bytes from inside),read,show (0#u8 !=0#u8)=false from rfl,
      Bool.false_eq_true,if_false,lift,bind_tc_ok]
    simpa only [r1_pool_adapter.owned.require_zero_loop,r1_pool_adapter.owned.require_zero_loop.body,lift,bind_tc_ok] using rest
#print axioms loop_zero

theorem source (bytes : Slice U8) (zero : ∀ b ∈ bytes.val,b=0#u8)
    (bound : bytes.val.length≤4096) : r1_pool_adapter.owned.require_zero bytes=ok (.Ok ()) := by
  unfold r1_pool_adapter.owned.require_zero
  rw [loop_zero bytes zero bound bytes.val.length 0#usize (by change 0+bytes.val.length=bytes.val.length;omega),bind_tc_ok]
#print axioms source
end AspisR1.JHe_ZeroGate
end
