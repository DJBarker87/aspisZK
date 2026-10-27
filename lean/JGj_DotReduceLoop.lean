import JGj_DotReduceStep
import OccupancyRangeTraversal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_DotReduceLoop
open Aeneas Aeneas.Std Result FIq_Native
open JGj_RawBounds
abbrev Range := core.ops.range.Range Usize
theorem factor (iter : Range) (sums raw : Raw) :
    field.qm31_m31_dot_loop1_loop1 iter sums raw=(do
      let (o,iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match o with
      | none => ok sums
      | some i => do
        let sums1 ← JGj_DotReduceStep.step sums raw i
        field.qm31_m31_dot_loop1_loop1 iter1 sums1 raw) := by
  rw [field.qm31_m31_dot_loop1_loop1.eq_def]
  simp only [JGj_DotReduceStep.step,lift,bind_tc_ok,bind_assoc_eq]
  rfl
theorem source (fuel : Nat) (iter : Range) (sums raw : Raw) (n : Nat)
    (he : iter.end.val≤4) (hf : iter.start.val+fuel=iter.end.val) (hn : n+fuel≤10)
    (hs : Bound sums (n*P)) :
    ∃ out,field.qm31_m31_dot_loop1_loop1 iter sums raw=ok out ∧ Bound out ((n+fuel)*P) := by
  induction fuel generalizing iter sums n with
  | zero =>
    refine ⟨sums,?_,by simpa only [Nat.add_zero] using hs⟩
    rw [factor,OccupancyRangeTraversal.next_done iter (by omega)]
    rfl
  | succ fuel ih =>
    obtain ⟨next,rnext,vstart,vend,_⟩ := OccupancyRangeTraversal.next_step iter (by omega)
    obtain ⟨sums1,rs,bs⟩ := JGj_DotReduceStep.source sums raw iter.start n (by change iter.start.val<4;omega) (by omega) hs
    obtain ⟨out,ro,bo⟩ := ih next sums1 (n+1) (by rw [vend];exact he) (by rw [vend,vstart];omega) (by omega) bs
    have h : n+1+fuel=n+(fuel+1) := by omega
    rw [h] at bo
    refine ⟨out,?_,bo⟩
    rw [factor,rnext]
    change (do let sums1 ← JGj_DotReduceStep.step sums raw iter.start;field.qm31_m31_dot_loop1_loop1 next sums1 raw)=ok out
    rw [rs,bind_tc_ok,ro]
#print axioms factor
#print axioms source
end AspisR1.JGj_DotReduceLoop
end
