import NFB_ZeroScan
set_option autoImplicit false
namespace NFB_ZeroFinite
open Aeneas Aeneas.Std Result ControlFlow

/-- Finite model retains the SAME slice and its exact native cursor; zero
short-circuit consumes the selected word and retains the untouched suffix. -/
def bounded : Nat → core.slice.iter.Iter U32 → Result (Bool × core.slice.iter.Iter U32)
 | 0,it => ok (false,it)
 | n+1,it => do
   let (next,after) ← core.slice.iter.IteratorSliceIter.next it
   match next with
   | none => ok (false,after)
   | some value => if decide (value=0#u32) then ok (true,after) else bounded n after

theorem next_active (it : core.slice.iter.Iter U32) (h : it.i < it.slice.val.length) :
    core.slice.iter.IteratorSliceIter.next it =
      ok (some it.slice.val[it.i],{it with i:=it.i+1}) := by
 unfold core.slice.iter.IteratorSliceIter.next
 split
 · rfl
 · rename_i hn; exact False.elim (hn h)

theorem next_end (it : core.slice.iter.Iter U32) (h : it.slice.val.length ≤ it.i) :
    core.slice.iter.IteratorSliceIter.next it=ok (none,it) := by
 unfold core.slice.iter.IteratorSliceIter.next
 split
 · rename_i hn
   have bad : it.i < it.slice.val.length := hn
   omega
 · rfl

/-- Induction is on remaining words, never on an unfolded concrete buffer. -/
theorem complete (it : core.slice.iter.Iter U32) (fuel : Nat)
    (remaining : it.i+fuel=it.slice.val.length) :
    loop NFB_ZeroScan.zeroStep (it,())=bounded fuel it := by
 induction fuel generalizing it with
 | zero =>
   rw [loop.eq_def]
   simp only [NFB_ZeroScan.zeroStep,next_end it (by omega),bind_tc_ok,bounded,uncurry]
 | succ fuel ih =>
   have active : it.i < it.slice.val.length := by omega
   have rest : ({it with i:=it.i+1} : core.slice.iter.Iter U32).i+fuel=it.slice.val.length := by
     simp only; omega
   rw [loop.eq_def]
   simp only [NFB_ZeroScan.zeroStep,next_active it active,bind_tc_ok,bounded,uncurry]
   by_cases hz : decide (it.slice.val[it.i] = 0#u32) = true
   · simp only [hz,if_true]
   · simpa only [hz,if_false] using ih {it with i:=it.i+1} rest

#print axioms next_active
#print axioms next_end
#print axioms complete
end NFB_ZeroFinite
