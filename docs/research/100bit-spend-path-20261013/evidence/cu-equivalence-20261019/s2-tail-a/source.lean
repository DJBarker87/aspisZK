import CuSavingsS2SourceTailStep
set_option autoImplicit false
namespace AspisR1.CuSavingsS2SourceTail
open Aeneas Aeneas.Std Result ControlFlow AspisR1S2Groups
open CuSavingsS2SourceArrays OccupancyRangeTraversal
variable [Shared]

def payload (low : Array E 16#usize) (masks : Masks) (coefficients : OldCoeffs)
    (group : Usize) (pair : E) : Result E := do
  let mask ← Array.index_usize masks group
  let i ← core.slice.Slice.iter low.to_slice
  let it ← core.iter.traits.iterator.Iterator.enumerate.trait_default
    (core.iter.traits.iterator.IteratorSliceIter E) i
  let weight ← old.grouped_inactive_pair_loop1_loop0 it mask zero
  let coeff ← Array.index_usize coefficients group
  let product ← field.wide_exact.WideExact.mul coeff weight
  field.wide_exact.WideExact.add pair product

theorem body_frame (low : Array E 16#usize) (masks : Masks) (coeff : OldCoeffs)
    (iter next : Range) (pair : E)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some iter.start,next)) :
    old.grouped_inactive_pair_loop1.body low masks coeff iter pair =
      (do let value ← payload low masks coeff iter.start pair
          .ok (.cont (next,value))) := by
  simp only [old.grouped_inactive_pair_loop1.body,hn,bind_tc_ok,lift]
  change (do
    let mask ← Array.index_usize masks iter.start
    let i ← core.slice.Slice.iter low.to_slice
    let it ← core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.iter.traits.iterator.IteratorSliceIter E) i
    let weight ← old.grouped_inactive_pair_loop1_loop0 it mask zero
    let value ← Array.index_usize coeff iter.start
    let product ← field.wide_exact.WideExact.mul value weight
    let out ← field.wide_exact.WideExact.add pair product
    Result.ok (ControlFlow.cont (β:=E) (next,out))) = _
  simp only [payload,bind_assoc_eq]

theorem source_loop (fuel : Nat) (low : Array E 16#usize) (masks : Masks)
    (oldCoeffs : OldCoeffs) (newCoeffs : NewCoeffs) (groups : Usize)
    (hc : Catalog 64 masks groups) (hv : CoeffEq oldCoeffs newCoeffs)
    (iter : Range) (he : iter.end.val=12) (hi : iter.start.val≤12)
    (hf : 12-iter.start.val=fuel) (pair : E) :
    new.s2_grouped_inactive_pair_loop1 iter low newCoeffs pair =
      old.grouped_inactive_pair_loop1 iter low masks oldCoeffs pair := by
  induction fuel generalizing iter pair with
  | zero =>
    have hn := next_done iter (by omega)
    have hnew : new.s2_grouped_inactive_pair_loop1.body low newCoeffs iter pair = .ok (.done pair) := by
      simp [new.s2_grouped_inactive_pair_loop1.body,hn]
    have hold : old.grouped_inactive_pair_loop1.body low masks oldCoeffs iter pair = .ok (.done pair) := by
      simp [old.grouped_inactive_pair_loop1.body,hn]
    conv_lhs => unfold new.s2_grouped_inactive_pair_loop1;rw [loop];dsimp only
    conv_rhs => unfold old.grouped_inactive_pair_loop1;rw [loop];dsimp only
    rw [hnew,hold]
  | succ fuel ih =>
    obtain ⟨next,hn,hinc,hend,_⟩ := next_step iter (by omega)
    have hold := body_frame low masks oldCoeffs iter next pair hn
    have hnew := (CuSavingsS2SourceTailStep.body_eq low masks oldCoeffs newCoeffs groups hc hv iter he pair).trans hold
    conv_lhs => unfold new.s2_grouped_inactive_pair_loop1;rw [loop];dsimp only
    conv_rhs => unfold old.grouped_inactive_pair_loop1;rw [loop];dsimp only
    rw [hnew,hold]
    cases hp : payload low masks oldCoeffs iter.start pair with
    | fail e => rfl
    | div => rfl
    | ok value =>
      exact ih next (by rw [hend];exact he) (by omega) (by omega) value

#print axioms body_frame
#print axioms source_loop
end AspisR1.CuSavingsS2SourceTail
