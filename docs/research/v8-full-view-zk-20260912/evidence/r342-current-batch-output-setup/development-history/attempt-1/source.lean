import AspisR340BatchOutputRaw
import AspisV8R19.R311BatchReverseLoopExecution

/-! Model the exact zero initialization and final index-zero write around the
actual extracted reverse loops. This is only the selected output fragment; it
does not prove the enclosing batch guards or source-to-Aeneas correspondence. -/
set_option autoImplicit false
namespace AspisV8R19.R342OutputSetup

open Aeneas Aeneas.Std Result ControlFlow WP
open AspisV8R15.ExactTowerBase
open AspisV8R19.ComplexBaseExecution (encodeBase)
open AspisV8R19.R311BatchReverseLoopExecution
open AspisR249R110Raw
open AspisR278PrivateInverseRaw
open AspisR305BatchReverseRaw.circle_norm.joined_inverse.line_norm.r110_norm
open AspisR340BatchOutputRaw

noncomputable section

/-- The model vector initialized to the source's B.ZERO value. -/
def zeroVec (xs : Slice U32) : VecU32 :=
  ⟨List.replicate xs.val.length
    AspisR278PrivateInverseRaw.circle_norm.joined_inverse.line_norm.r110_norm.B.ZERO,
    by simpa using xs.property⟩

/-- The iterator produced by the exact default `rev` call in the fragment. -/
def outputReverseRange (xs : Slice U32) : ReverseRange :=
  ⟨{ start := 1#usize, «end» := Slice.len xs }⟩

theorem from_elem_zeroVec (xs : Slice U32) :
    alloc.vec.from_elem
      AspisR340BatchOutputRaw.circle_norm.joined_inverse.line_norm.r110_norm.B.Insts.CoreCloneClone
      AspisR278PrivateInverseRaw.circle_norm.joined_inverse.line_norm.r110_norm.B.ZERO
      (Slice.len xs) = .ok (zeroVec xs) := by
  have hclone :
      AspisR340BatchOutputRaw.circle_norm.joined_inverse.line_norm.r110_norm.B.Insts.CoreCloneClone.clone
        AspisR278PrivateInverseRaw.circle_norm.joined_inverse.line_norm.r110_norm.B.ZERO =
      .ok AspisR278PrivateInverseRaw.circle_norm.joined_inverse.line_norm.r110_norm.B.ZERO := by
    rfl
  obtain ⟨v, hrun, hrep, _hlen⟩ := spec_imp_exists
    (alloc.vec.from_elem_spec
      AspisR340BatchOutputRaw.circle_norm.joined_inverse.line_norm.r110_norm.B.Insts.CoreCloneClone
      AspisR278PrivateInverseRaw.circle_norm.joined_inverse.line_norm.r110_norm.B.ZERO
      (Slice.len xs) hclone)
  have hv : v = zeroVec xs := by
    apply Subtype.ext
    simpa [zeroVec, Slice.len_val] using hrep
  rw [hv] at hrun
  exact hrun

/-- The exact default reverse adapter wraps the requested range unchanged. -/
theorem output_reverse_range_default (xs : Slice U32) :
    core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
      { start := 1#usize, «end» := Slice.len xs } =
      .ok (outputReverseRange xs) := by
  rfl

theorem zeroVec_length (xs : Slice U32) : (zeroVec xs).length = xs.val.length := by
  simp [zeroVec]

theorem reverseModel_output_length (f g : Nat → M31Exact) (n : Nat)
    (x : M31Exact) (ox : VecU32) :
    (reverseModel f g n x ox).2.length = ox.length := by
  induction n generalizing x ox with
  | zero => rfl
  | succ n ih =>
      calc
        (reverseModel f g (n + 1) x ox).2.length =
            (reverseModel f g n (x * f (n + 1))
              (setNat ox (n + 1) (encodeBase (g n * x)))).2.length := by
                rfl
        _ = (setNat ox (n + 1) (encodeBase (g n * x))).length :=
              ih _ _
        _ = ox.length := setNat_length ox (n + 1) _

theorem selectedOutput1_eq_selectedOutput0
    (ys : Slice U32) (py : VecU32) (iy : U32) :
    selectedOutput1 ys py iy = selectedOutput0 ys py iy := by
  rfl

/-- Exact execution of output initialization, reverse loop 2, and the final
index-zero replacement. The input and prefix reads are the only loop premises. -/
theorem selectedOutput0_model
    (xs : Slice U32) (px : VecU32) (f g : Nat → M31Exact)
    (x : M31Exact) (hnonempty : 0 < xs.val.length)
    (hxs : ∀ j, 1 ≤ j → j < xs.val.length →
      xs.val[j]? = some (encodeBase (f j)))
    (hpx : ∀ j, j < xs.val.length - 1 →
      px.val[j]? = some (encodeBase (g j))) :
    selectedOutput0 xs px (encodeBase x) =
      .ok (setNat
        (reverseModel f g (xs.val.length - 1) x (zeroVec xs)).2
        0
        (encodeBase
          (reverseModel f g (xs.val.length - 1) x (zeroVec xs)).1)) := by
  let n := xs.val.length - 1
  let iter := outputReverseRange xs
  let model := reverseModel f g n x (zeroVec xs)
  have hstart : iter.iter.start.val = 1 := by
    simp [iter, outputReverseRange]
  have hend : iter.iter.end.val = n + 1 := by
    dsimp [iter, outputReverseRange, n]
    rw [Slice.len_val]
    omega
  have hxs' : ∀ j, 1 ≤ j → j ≤ n →
      xs.val[j]? = some (encodeBase (f j)) := by
    intro j hj1 hjn
    apply hxs j hj1
    dsimp [n]
    omega
  have hpx' : ∀ j, j < n →
      px.val[j]? = some (encodeBase (g j)) := by
    intro j hj
    exact hpx j (by simpa [n] using hj)
  have hcapacity : n < (zeroVec xs).length := by
    rw [zeroVec_length]
    dsimp [n]
    omega
  have hloop : batch_loop2 iter xs px (encodeBase x) (zeroVec xs) =
      .ok (encodeBase model.1, model.2) := by
    simpa [model] using
      batch_loop2_reverseModel f g n xs px (zeroVec xs) iter x
        hstart hend hxs' hpx' hcapacity
  have hmodel_len : model.2.length = xs.val.length := by
    dsimp [model]
    rw [reverseModel_output_length, zeroVec_length]
  have hindex : (0#usize).val < model.2.length := by
    rw [hmodel_len]
    have hzero : (0#usize).val = 0 := by simp
    omega
  obtain ⟨⟨old, back⟩, hmut, _hold, hback⟩ := spec_imp_exists
    (alloc.vec.Vec.index_mut_usize_spec model.2 0#usize hindex)
  have hset : setNat model.2 0 (encodeBase model.1) =
      alloc.vec.Vec.set model.2 0#usize (encodeBase model.1) :=
    setNat_eq_vec_set model.2 0 (encodeBase model.1) 0#usize (by simp)
  unfold selectedOutput0
  simp only [from_elem_zeroVec, output_reverse_range_default, bind_tc_ok]
  rw [hloop]
  simp only [bind_tc_ok, alloc.vec.Vec.index_mut_slice_index, hmut, hback]
  rw [← hset]

theorem selectedOutput1_model
    (ys : Slice U32) (py : VecU32) (f g : Nat → M31Exact)
    (x : M31Exact) (hnonempty : 0 < ys.val.length)
    (hys : ∀ j, 1 ≤ j → j < ys.val.length →
      ys.val[j]? = some (encodeBase (f j)))
    (hpy : ∀ j, j < ys.val.length - 1 →
      py.val[j]? = some (encodeBase (g j))) :
    selectedOutput1 ys py (encodeBase x) =
      .ok (setNat
        (reverseModel f g (ys.val.length - 1) x (zeroVec ys)).2
        0
        (encodeBase
          (reverseModel f g (ys.val.length - 1) x (zeroVec ys)).1)) := by
  rw [selectedOutput1_eq_selectedOutput0]
  exact selectedOutput0_model ys py f g x hnonempty hys hpy

#print axioms zeroVec
#print axioms outputReverseRange
#print axioms from_elem_zeroVec
#print axioms output_reverse_range_default
#print axioms zeroVec_length
#print axioms reverseModel_output_length
#print axioms selectedOutput1_eq_selectedOutput0
#print axioms selectedOutput0_model
#print axioms selectedOutput1_model

end
end AspisV8R19.R342OutputSetup
