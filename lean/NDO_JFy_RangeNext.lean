import RPv_FIx_PreweightedLoop
set_option autoImplicit false
namespace AspisR1.JFy_RangeNext
open Aeneas Aeneas.Std Result
abbrev R := core.ops.range.RangeInclusive Usize

theorem source (r : R) (live : r.exhausted=false) (h : r.start.val<r.end.val) :
    ∃ r',core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next core.iter.range.StepUsize r=ok (some r.start,r') ∧
      r'.start.val=r.start.val+1 ∧ r'.end=r.end ∧ r'.exhausted=false := by
  obtain ⟨⟨o,r'⟩,call,post⟩ := WP.spec_imp_exists
    (core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next_Usize_spec r)
  have ne : ¬ (r.exhausted=true ∨ r.end.val<r.start.val) := by simp only [live,Bool.false_eq_true,false_or];omega
  simp only [if_neg ne,if_pos h] at post
  obtain ⟨rfl,hs,he,hx⟩ := post
  exact ⟨r',call,hs,he,hx⟩
#print axioms source
end AspisR1.JFy_RangeNext
