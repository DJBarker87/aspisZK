import AspisR328PrefixInitializationRaw
import AspisV8R19.R321BatchPrefixLoopExecution
import AspisV8R19.R326PrefixProductSelectors

/-! Successful selected source-contiguous prefix initialization. Nonempty and
canonical source reads are explicit local conditions; vector capacity is
proved from the original valid Slice bound. No whole batch guard is assumed. -/
set_option autoImplicit false
namespace AspisV8R19.R329PrefixInitializationExecution
open Aeneas Aeneas.Std Result ControlFlow WP
open AspisV8R15.ExactTowerBase
open AspisV8R19.ComplexBaseExecution (encodeBase)
open AspisV8R19.R321BatchPrefixLoopExecution
open AspisR328PrefixInitializationRaw
noncomputable section

theorem selectedPrefix0_empty (xs : Slice U32) (hempty : xs.val = []) :
    selectedPrefix0 xs = .fail .arrayOutOfBounds := by
  simp only [selectedPrefix0, Slice.index_usize, Slice.getElem?_Usize_eq,
    show (0#usize).val = 0 from by simp, hempty, List.getElem?_nil, bind_tc_fail]

theorem selectedPrefix0_products (xs : Slice U32) (f : Nat → M31Exact)
    (hnonempty : 0 < xs.val.length)
    (hxs : ∀ j, j < xs.val.length → xs.val[j]? = some (encodeBase (f j))) :
    ∃ out : alloc.vec.Vec U32,
      out.val = [encodeBase (f 0)] ++
        prefixValues (fun j => f (j + 1)) 0 (xs.val.length - 1) (f 0) ∧
      selectedPrefix0 xs = .ok out := by
  let v0 : alloc.vec.Vec U32 := alloc.vec.Vec.with_capacity U32 (Slice.len xs)
  have hv0 : v0.val = [] := by rfl
  have h0 : Slice.index_usize xs 0#usize = .ok (encodeBase (f 0)) := by
    simp only [Slice.index_usize, Slice.getElem?_Usize_eq,
      show (0#usize).val = 0 from by simp, hxs 0 hnonempty]
  obtain ⟨v1, hvpush, hv1⟩ := spec_imp_exists
    (alloc.vec.Vec.push_spec v0 (encodeBase (f 0)) (by rw [hv0]; scalar_tac))
  have hv1list : v1.val = [encodeBase (f 0)] := by simpa only [hv0, List.nil_append] using hv1
  let range : core.ops.range.RangeFrom Usize := ⟨1#usize⟩
  obtain ⟨s, hs, hsval, hslen⟩ := spec_imp_exists
    (core.slice.index.SliceIndexRangeFromUsizeSlice.index.step_spec range xs
      (by dsimp [range]; change 1 ≤ xs.val.length; omega))
  have hsval1 : s.val = xs.val.drop 1 := by
    simpa only [range, show (1#usize).val = 1 from by simp] using hsval
  have hslen1 : s.val.length = xs.val.length - 1 := by
    simpa only [range, show (1#usize).val = 1 from by simp] using hslen
  let iter : core.slice.iter.Iter U32 := ⟨s, 0⟩
  have hread : ∀ j, iter.i ≤ j → j < iter.slice.val.length →
      iter.slice.val[j]? = some (encodeBase ((fun j => f (j + 1)) j)) := by
    intro j _ hj
    change s.val[j]? = _
    rw [hsval1, List.getElem?_drop]
    have hb : 1 + j < xs.val.length := by dsimp [iter] at hj; rw [hslen1] at hj; omega
    simpa only [Nat.add_comm] using hxs (1 + j) hb
  have hlast : v1.val.getLast? = some (encodeBase (f 0)) := by rw [hv1list]; simp
  have hcap : v1.val.length + (xs.val.length - 1) ≤ Usize.max := by
    rw [hv1list]
    have hb := xs.property
    simp only [List.length_singleton]
    omega
  obtain ⟨out, hout, hloop⟩ := batch_loop0_prefixValues
    (fun j => f (j + 1)) (xs.val.length - 1) iter v1 (f 0)
    (by dsimp [iter]; simpa only [Nat.zero_add] using hslen1.symm)
    hread hlast hcap
  refine ⟨out, ?_, ?_⟩
  · simpa only [iter, hv1list] using hout
  · simp only [selectedPrefix0, h0, bind_tc_ok]
    change (do
      let v1 ← alloc.vec.Vec.push v0 (encodeBase (f 0))
      let s ← core.slice.index.SliceIndexRangeFromUsizeSlice.index range xs
      let iter ← SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter s
      let out ← AspisR318BatchPrefixRaw.circle_norm.joined_inverse.line_norm.r110_norm.batch_loop0 iter v1
      .ok out) = .ok out
    simp only [hvpush, hs, bind_tc_ok,
      SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter]
    change (do
      let out ← AspisR318BatchPrefixRaw.circle_norm.joined_inverse.line_norm.r110_norm.batch_loop0 iter v1
      .ok out) = .ok out
    rw [hloop]
    rfl

#print axioms selectedPrefix0_empty
#print axioms selectedPrefix0_products
end
end AspisV8R19.R329PrefixInitializationExecution
