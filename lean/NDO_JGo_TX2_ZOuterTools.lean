import RPz7_FIn_WeightsInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_ZOuterTools
open Aeneas Aeneas.Std Result ControlFlow FIn_WeightsExtract
abbrev Q := field.QM31
abbrev Row := Array (Array Q 4#usize) 5#usize
abbrev Factors := Array Row 5#usize
abbrev Range := core.ops.range.Range Usize
attribute [local irreducible] weights_new_loop1_loop0

theorem source (z : Array circle.SecureCirclePoint 2#usize) (r next : Range)
    (before after : Factors) (k index : Usize) (scp : circle.SecureCirclePoint)
    (product x : Q) (row written : Row) (back : Row → Factors)
    (nextCall : core.iter.range.IteratorRange.next core.iter.range.StepUsize r=ok (some k,next))
    (readPoint : Array.index_usize z k=ok scp)
    (mul : field.QM31.mul scp.x scp.y=ok product)
    (offset : Usize.wrapping_add 3#usize k=index)
    (readRow : Array.index_mut_usize before index=ok (row,back))
    (writeRow : Array.update row 0#usize (Array.make 4#usize [field.QM31.ONE,scp.y,scp.x,product])=ok written)
    (square : double scp.x=ok x)
    (inner : weights_new_loop1_loop0 {start:=1#usize,«end»:=5#usize} (back written) k x=ok after) :
    weights_new_loop1.body z r before=ok (.cont (next,after)) := by
  unfold weights_new_loop1.body
  rw [nextCall,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [readPoint,bind_tc_ok,mul,bind_tc_ok]
  simp only [lift,bind_tc_ok,offset]
  rw [readRow,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [writeRow,bind_tc_ok,square,bind_tc_ok,inner,bind_tc_ok]
#print axioms source
end AspisR1.JGo_TX2_ZOuterTools
end
