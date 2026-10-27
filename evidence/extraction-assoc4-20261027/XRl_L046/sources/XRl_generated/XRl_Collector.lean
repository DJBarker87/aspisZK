import XRk_ResultTools
open Aeneas Aeneas.Std Result
namespace XRl_Collector
/-- Successful collection counts every yielded item exactly once. The measure
is an explicit property of the SAME iterator dictionary, including its terminal
step; callback failure/divergence is not converted into a successful result. -/
theorem length {I T : Type} (it : core.iter.traits.iterator.Iterator I T)
    (remaining : I → Nat)
    (terminal : ∀ s next, it.next s = ok (none,next) → remaining s = 0)
    (advance : ∀ s item next, it.next s = ok (some item,next) → remaining s = remaining next + 1)
    (s : I) (acc out : List T)
    (run : alloc.vec.FromIteratorVec.iterToList it s acc = ok out) :
    out.length = acc.length + remaining s := by
  suffices ∀ n s acc, remaining s=n →
      alloc.vec.FromIteratorVec.iterToList it s acc=ok out →
      out.length=acc.length+remaining s from this (remaining s) s acc rfl run
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s acc size run
    rw [alloc.vec.FromIteratorVec.iterToList] at run
    cases step : it.next s with
    | fail e => simp only [step,bind_tc_fail] at run; cases run
    | div => simp only [step,bind_tc_div] at run; cases run
    | ok pair =>
      rcases pair with ⟨item,next⟩
      cases item with
      | none =>
        simp only [step,bind_tc_ok] at run
        have same := Result.ok.inj run
        rw [← same,List.length_reverse,terminal s next step,Nat.add_zero]
      | some item =>
        simp only [step,bind_tc_ok] at run
        have count := advance s item next step
        have tail := ih (remaining next) (by omega) next (item::acc) rfl run
        simp only [List.length_cons] at tail
        omega
#print axioms length
end XRl_Collector
