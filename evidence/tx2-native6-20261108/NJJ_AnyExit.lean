import NJJ_Any
set_option autoImplicit false
noncomputable section
namespace NJJ_AnyExit
open Aeneas Aeneas.Std Result

theorem next_none (it rest : core.slice.iter.Iter U8)
 (step : core.slice.iter.IteratorSliceIter.next it=ok (none,rest)) :
 rest=it ∧ it.slice.val.length ≤ it.i := by
 unfold core.slice.iter.IteratorSliceIter.next at step
 split at step
 · cases step
 · rename_i ended
   cases step
   constructor
   · rfl
   · exact Nat.le_of_not_gt ended

theorem next_some (it rest : core.slice.iter.Iter U8) (b : U8)
 (step : core.slice.iter.IteratorSliceIter.next it=ok (some b,rest)) :
 rest.slice=it.slice ∧ rest.i=it.i+1 := by
 unfold core.slice.iter.IteratorSliceIter.next at step
 split at step <;> cases step
 exact ⟨rfl,rfl⟩

/-- False means actual exhaustion or exhaustion of the explicit fuel. -/
theorem false_exit (n : Nat) (it out : core.slice.iter.Iter U8)
 (returned : NJJ_Any.run n it=ok (false,out)) :
 it.slice.val.length≤out.i ∨ out.i=it.i+n := by
 induction n generalizing it with
 | zero => cases returned;exact Or.inr (by omega)
 | succ n ih =>
   unfold NJJ_Any.run at returned
   cases step : core.slice.iter.IteratorSliceIter.next it with
   | fail err => simp only [step,bind_tc_fail] at returned;cases returned
   | div => simp only [step,bind_tc_div] at returned;cases returned
   | ok pair =>
     rcases pair with ⟨value,rest⟩
     rw [step] at returned
     simp only [bind_tc_ok] at returned
     cases value with
     | none =>
       have info:=next_none it rest step
       cases returned
       exact Or.inl (by rw [info.1];exact info.2)
     | some b =>
       change (if b != 0#u8 then ok (true,rest) else NJJ_Any.run n rest)=ok (false,out) at returned
       split at returned
       · cases returned
       · have info:=next_some it rest b step
         rcases ih rest returned with exhausted | fuel
         · exact Or.inl (by rw [← info.1];exact exhausted)
         · exact Or.inr (by omega)

/-- The length+1 fuel in the actual installed library model cannot hide an
unfinished iterator on a false return. Backing bytes are covered by Any.frame. -/
theorem exhausted (it out : core.slice.iter.Iter U8)
 (returned : NJJ_Any.any it=ok (false,out)) :
 it.slice.val.length≤out.i := by
 rcases false_exit (it.slice.val.length+1) it out returned with done | fuel
 · exact done
 · omega

#print axioms next_none
#print axioms next_some
#print axioms false_exit
#print axioms exhausted
end NJJ_AnyExit
