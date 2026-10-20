import CuSavingsS2SourceCoefficientStep
import CuSavingsLoopRelation
set_option autoImplicit false
namespace AspisR1.CuSavingsS2SourceTailStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1S2Groups
open CuSavingsS2SourceArrays OccupancyRangeTraversal
abbrev Iter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter E)
variable [Shared]

theorem weight_body (group : Usize) (mask : U16)
    (hm : Array.index_usize AspisR1S2Groups.new.S2_INACTIVE_MASKS group = .ok mask) (iter : Iter) (weight : E) :
    AspisR1S2Groups.new.s2_grouped_inactive_pair_loop1_loop0.body group iter weight =
      AspisR1S2Groups.old.grouped_inactive_pair_loop1_loop0.body mask iter weight := by
  unfold AspisR1S2Groups.new.s2_grouped_inactive_pair_loop1_loop0.body AspisR1S2Groups.old.grouped_inactive_pair_loop1_loop0.body
  apply (bind_eq_iff _ _ _).mpr
  intro pair hp
  rcases pair with ⟨opt,next⟩
  cases opt with
  | none => rfl
  | some p =>
    rcases p with ⟨bit,challenge⟩
    change (do
      let mask ← Array.index_usize AspisR1S2Groups.new.S2_INACTIVE_MASKS group
      let one ← 1#u16 <<< bit
      let flag ← lift (mask &&& one)
      if flag != 0#u16 then
        let out ← field.wide_exact.WideExact.add weight challenge
        Result.ok (ControlFlow.cont (β:=E) (next,out))
      else Result.ok (ControlFlow.cont (β:=E) (next,weight))) = _
    rw [hm,bind_tc_ok]
    rfl

theorem weight_loop (group : Usize) (mask : U16)
    (hm : Array.index_usize AspisR1S2Groups.new.S2_INACTIVE_MASKS group = .ok mask) (iter : Iter) (weight : E) :
    AspisR1S2Groups.new.s2_grouped_inactive_pair_loop1_loop0 iter group weight =
      AspisR1S2Groups.old.grouped_inactive_pair_loop1_loop0 iter mask weight := by
  have hb : (fun (it,w) => AspisR1S2Groups.new.s2_grouped_inactive_pair_loop1_loop0.body group it w) =
      (fun (it,w) => AspisR1S2Groups.old.grouped_inactive_pair_loop1_loop0.body mask it w) := by
    funext state
    rcases state with ⟨it,w⟩
    exact weight_body group mask hm it w
  unfold AspisR1S2Groups.new.s2_grouped_inactive_pair_loop1_loop0 AspisR1S2Groups.old.grouped_inactive_pair_loop1_loop0
  exact congrArg (fun body => loop body (iter,weight)) hb

theorem body_eq (low : Array E 16#usize) (masks : Masks) (old : OldCoeffs) (new : NewCoeffs)
    (groups : Usize) (hc : Catalog 64 masks groups) (hv : CoeffEq old new)
    (iter : Range) (he : iter.end.val=12) (pair : E) :
    AspisR1S2Groups.new.s2_grouped_inactive_pair_loop1.body low new iter pair =
      AspisR1S2Groups.old.grouped_inactive_pair_loop1.body low masks old iter pair := by
  by_cases halt : iter.start.val ≥ iter.end.val
  · have hn := next_done iter halt
    simp [AspisR1S2Groups.new.s2_grouped_inactive_pair_loop1.body,AspisR1S2Groups.old.grouped_inactive_pair_loop1.body,hn]
  · obtain ⟨next,hn,hinc,hend,_⟩ := next_step iter (by omega)
    have hg : iter.start.val<12 := by omega
    obtain ⟨mask,hm,hmv⟩ := CuSavingsS2SourceTables.mask_source iter.start hg
    have hn12 : groups.val=12 := hc.1.trans CuSavingsS2SourceTables.seen_end
    have hmask : lookup masks 0#u16 iter.start.val=mask := UScalar.eq_of_val_eq
      ((hc.2 iter.start.val (by omega)).trans hmv.symm)
    have hread : Array.index_usize masks iter.start = .ok mask := by
      simpa only [hmask] using read masks 0#u16 iter.start (by scalar_tac)
    simp only [AspisR1S2Groups.new.s2_grouped_inactive_pair_loop1.body,AspisR1S2Groups.old.grouped_inactive_pair_loop1.body,hn,bind_tc_ok]
    change (do
      let s ← lift (Array.to_slice low)
      let i ← core.slice.Slice.iter s
      let it ← core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorSliceIter E) i
      let weight ← AspisR1S2Groups.new.s2_grouped_inactive_pair_loop1_loop0 it iter.start zero
      let coeff ← Array.index_usize new iter.start
      let product ← field.wide_exact.WideExact.mul coeff weight
      let out ← field.wide_exact.WideExact.add pair product
      Result.ok (ControlFlow.cont (β:=E) (next,out))) = (do
      let mask ← Array.index_usize masks iter.start
      let s ← lift (Array.to_slice low)
      let i ← core.slice.Slice.iter s
      let it ← core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorSliceIter E) i
      let weight ← AspisR1S2Groups.old.grouped_inactive_pair_loop1_loop0 it mask zero
      let coeff ← Array.index_usize old iter.start
      let product ← field.wide_exact.WideExact.mul coeff weight
      let out ← field.wide_exact.WideExact.add pair product
      Result.ok (ControlFlow.cont (β:=E) (next,out)))
    simp only [hread,bind_tc_ok,weight_loop iter.start mask hm,
      read new zero iter.start (by scalar_tac),read old zero iter.start (by scalar_tac),hv iter.start.val hg]

#print axioms weight_body
#print axioms weight_loop
#print axioms body_eq
end AspisR1.CuSavingsS2SourceTailStep
