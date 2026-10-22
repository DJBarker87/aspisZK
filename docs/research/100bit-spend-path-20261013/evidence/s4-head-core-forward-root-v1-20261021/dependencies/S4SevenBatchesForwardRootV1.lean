import S4HeadOuterForwardRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsSevenBatchesForwardRootV1
open AspisR1FastDotsHeadLimbForwardRootV1 (Ops)
open AspisR1FastDotsHeadReadForwardRootV1 (Wide)
open AspisR1FastDotsActualInnerLoopLinearBoundV1 (cell)
open AspisR1FastDotsHeadBatchTermsForwardRootV1 (ParsedAt)
open AspisR1FastDotsCurrentHeadTermForwardRootV1 (install)
open AspisR1FastDotsLimbFoldForwardRootV1 (limbCap)
open AspisR1FastDotsHeadBatchBodyForwardRootV1 (StepBy)
open AspisR1FastDotsHeadOuterForwardRootV1 (OuterLoop outer_loop_forward)
def initialIterator : StepBy :=
  {iter:={start:=0#usize,«end»:=26#usize},step_by:=4#usize}

theorem seven_batches_forward
    (base : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (hcoords : ∀ j : Fin 29, AspisR1FastDotsWideLimbCanonical.CoordinateBound
      (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    (hparsed : ∀ term : Usize, term.val<26 → ParsedAt a g slot term) :
    ∃ out : Array Std.U64 8#usize,
      core.iter.traits.iterator.Iterator.step_by.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        {start:=0#usize,«end»:=26#usize} 4#usize = .ok initialIterator ∧
      OuterLoop (install base) initialIterator a g slot (Array.repeat 8#usize 0#u64) = .ok out ∧
      (∀ j : Fin 8, cell out j≤56*limbCap) := by
  have hi : core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      {start:=0#usize,«end»:=26#usize} 4#usize = .ok initialIterator := by
    simp [initialIterator,core.iter.traits.iterator.Iterator.step_by.trait_default,
      core.iter.traits.iterator.Iterator.step_by.default]
  have hz : ∀ j : Fin 8, cell (Array.repeat 8#usize 0#u64) j≤0*limbCap := by
    intro j
    change ((List.replicate 8 (0#u64))[j.val]'(by simpa only [List.length_replicate] using j.isLt)).val≤0*limbCap
    rw [List.getElem_replicate]
    exact Nat.le_refl 0
  obtain ⟨out,hl,hb⟩ := outer_loop_forward base a g slot initialIterator
    (Array.repeat 8#usize 0#u64) 0 (by decide) rfl rfl (by decide) hcoords hparsed hz
  exact ⟨out,hi,hl,by simpa [initialIterator] using hb⟩

#print axioms seven_batches_forward
end AspisR1FastDotsSevenBatchesForwardRootV1
