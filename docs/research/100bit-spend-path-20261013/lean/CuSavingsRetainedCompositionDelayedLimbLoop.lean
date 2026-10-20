import CuSavingsRetainedCompositionDelayedArrays
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedCompositionDelayedLimbLoop
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1RetainedDots AspisV8R17.RawReducer
open CuSavingsRetainedCompositionDelayedArrays CuSavingsRetainedCompositionDelayedScalar CuSavingsResidues OccupancyRangeTraversal

theorem body_step (sums : Raw) (iter next : CuSavingsRetainedCompositionDelayedArrays.Range) (old : Canon) (raw : Raw)
    (i : Usize) (hi : i.val < 8)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some i,next))
    (o : U32) (r : U64)
    (ho : (do let s ← field.M31.reduce_u64 (wordAt sums ⟨i.val,hi⟩)
              field.M31.add (wordAt old ⟨i.val,hi⟩) s) = .ok o)
    (hr : foldAdd (wordAt raw ⟨i.val,hi⟩) (wordAt sums ⟨i.val,hi⟩) = .ok r) :
    old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1.body sums iter old = .ok (.cont (next,old.set i o)) ∧
    new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1.body sums iter raw = .ok (.cont (next,raw.set i r)) := by
  constructor
  · have factor : old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1.body sums iter old = (do
        let o ← (do let s ← field.M31.reduce_u64 (wordAt sums ⟨i.val,hi⟩)
                    field.M31.add (wordAt old ⟨i.val,hi⟩) s)
        let a ← Array.update old i o
        .ok (.cont (next,a))) := by
      simp only [old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1.body,hn,bind_tc_ok]
      change (do
        let m ← Array.index_usize old i
        let sum ← Array.index_usize sums i
        let reduced ← field.M31.reduce_u64 sum
        let o ← field.M31.add m reduced
        let a ← Array.update old i o
        Result.ok (ControlFlow.cont (β := Canon) (next,a))) = _
      simp only [read old i hi,read sums i hi,bind_tc_ok,bind_assoc_eq]
    rw [factor,ho,bind_tc_ok,update old i hi o,bind_tc_ok]
  · have factor : new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1.body sums iter raw = (do
        let r ← foldAdd (wordAt raw ⟨i.val,hi⟩) (wordAt sums ⟨i.val,hi⟩)
        let a ← Array.update raw i r
        .ok (.cont (next,a))) := by
      simp only [new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1.body,hn,bind_tc_ok]
      change (do
        let sum ← Array.index_usize sums i
        let high ← sum >>> 31#i32
        let folded ← (sum &&& 2147483647#u64) + high
        let original ← Array.index_usize raw i
        let r ← original + folded
        let a ← Array.update raw i r
        Result.ok (ControlFlow.cont (β := Raw) (next,a))) = _
      simp only [read raw i hi,read sums i hi,bind_tc_ok,
        foldAdd,ExtractedCurrentReducer.foldExecution,
        ExtractedCurrentReducer.mask64,ExtractedCurrentReducer.mask32,lift,bind_assoc_eq]
      rfl
    rw [factor,hr,bind_tc_ok,update raw i hi r,bind_tc_ok]

theorem source_both (fuel : Nat) (iter : CuSavingsRetainedCompositionDelayedArrays.Range) (sums : Raw)
    (old : Canon) (raw : Raw) (count : Nat) (hc : count < 7)
    (he : iter.end.val = 8) (hi : iter.start.val ≤ 8)
    (hf : 8-iter.start.val = fuel) (h : State count iter.start.val old raw) :
    ∃ (o : Canon) (r : Raw), old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1 iter old sums = .ok o ∧
      new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1 iter raw sums = .ok r ∧ State count 8 o r := by
  induction fuel generalizing iter old raw with
  | zero =>
    have hend : iter.start.val ≥ iter.end.val := by omega
    have hn := next_done iter hend
    refine ⟨old,raw,?_,?_,?_⟩
    · unfold old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1
      rw [loop]
      simp only [old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1.body,hn,bind_tc_ok]
      rfl
    · unfold new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1
      rw [loop]
      simp only [new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1.body,hn,bind_tc_ok]
      rfl
    · have hs : iter.start.val = 8 := by omega
      simpa only [hs] using h
  | succ fuel ih =>
    have his : iter.start.val < 8 := by omega
    obtain ⟨next,hn,hinc,hend,_⟩ := next_step iter (by omega)
    have entry := h ⟨iter.start.val,his⟩
    have hraw : (wordAt raw ⟨iter.start.val,his⟩).val < (count+1)*FoldBound := by
      simpa only [Nat.lt_irrefl,↓reduceIte] using entry.2
    obtain ⟨o,r,ho,hr,her,hrb⟩ := scalar_step (wordAt old ⟨iter.start.val,his⟩)
      (wordAt raw ⟨iter.start.val,his⟩) (wordAt sums ⟨iter.start.val,his⟩) count hc entry.1 hraw
    have steps := body_step sums iter next old raw iter.start his hn o r ho hr
    have hstate := state_step count iter.start.val old raw iter.start his rfl h o r her hrb
    have hstate1 : State count next.start.val (old.set iter.start o) (raw.set iter.start r) := by
      rw [hinc];exact hstate
    obtain ⟨out,res,hold,hnew,hfinal⟩ := ih next (old.set iter.start o) (raw.set iter.start r)
      (by rw [hend];exact he) (by omega) (by omega) hstate1
    refine ⟨out,res,?_,?_,hfinal⟩
    · unfold old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1
      rw [loop]
      dsimp only
      rw [steps.1]
      exact hold
    · unfold new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1
      rw [loop]
      dsimp only
      rw [steps.2]
      exact hnew

#print axioms body_step
#print axioms source_both
end AspisR1.CuSavingsRetainedCompositionDelayedLimbLoop
