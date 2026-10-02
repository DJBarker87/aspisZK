import AspisV8R19.R306BatchReverseStepExecution

/-! The exact reverse-loop recurrence, using a model-only Nat-indexed Vec
update. This file is a draft and has not been compiled. `setNat` is notation
for a same-length list update inside the existing Vec representation; it does
not replace or assume behavior for the extracted `Vec.set`. The bridge below
relates it to the actual Usize-indexed `Vec.set` at an in-range index. -/
set_option autoImplicit false
namespace AspisV8R19.R311BatchReverseLoopScratch

open Aeneas Aeneas.Std Result ControlFlow
open AspisV8R15.ExactTowerBase
open AspisV8R19.ComplexBaseExecution (encodeBase)
open AspisV8R19.R306BatchReverseStepExecution
open AspisR305BatchReverseRaw.circle_norm.joined_inverse.line_norm.r110_norm

noncomputable section

abbrev VecU32 := alloc.vec.Vec U32
abbrev ReverseRange := core.iter.adapters.rev.Rev (core.ops.range.Range Usize)

/-- Model-only Nat-indexed vector update, preserving the Vec length bound. -/
def setNat (out : VecU32) (j : Nat) (w : U32) : VecU32 :=
  ⟨out.val.set j w, by simpa only [List.length_set] using out.property⟩

theorem setNat_eq_vec_set (out : VecU32) (j : Nat) (w : U32)
    (i : Usize) (hi : i.val = j) :
    setNat out j w = out.set i w := by
  apply Subtype.ext
  simp [setNat, alloc.vec.Vec.set, hi]

theorem setNat_length (out : VecU32) (j : Nat) (w : U32) :
    (setNat out j w).length = out.length := by
  simp [setNat]

/-- Mathematical reverse recurrence matching the success branch of the
extracted reverse iterator: at count `n+1`, read `f (n+1)`, write the
corresponding `g n * x` value at output index `n+1`, then recurse. -/
def reverseModel (f g : Nat → M31Exact) :
    Nat → M31Exact → VecU32 → (M31Exact × VecU32)
  | 0, x, out => (x, out)
  | n + 1, x, out =>
      reverseModel f g n (x * f (n + 1))
        (setNat out (n + 1) (encodeBase (g n * x)))

theorem batch_loop2_reverseModel
    (f g : Nat → M31Exact) (n : Nat)
    (xs : Slice U32) (px ox : VecU32) (iter : ReverseRange)
    (x : M31Exact)
    (hstart : iter.iter.start.val = 1)
    (hend : iter.iter.end.val = n + 1)
    (hxs : ∀ j, 1 ≤ j → j ≤ n →
      xs.val[j]? = some (encodeBase (f j)))
    (hpx : ∀ j, j < n →
      px.val[j]? = some (encodeBase (g j)))
    (hlen : n < ox.length) :
    batch_loop2 iter xs px (encodeBase x) ox =
      .ok (encodeBase (reverseModel f g n x ox).1,
        (reverseModel f g n x ox).2) := by
  induction n generalizing iter x ox with
  | zero =>
      have hstop : iter.iter.end.val ≤ iter.iter.start.val := by omega
      rw [batch_loop2, loop.eq_def]
      rw [body2_done xs px ox iter (encodeBase x) hstop]
      simp [reverseModel]
  | succ n ih =>
      have hstep : iter.iter.start.val < iter.iter.end.val := by omega
      have hend_pos : 1 ≤ iter.iter.end.val := by omega
      let i : Usize := Usize.wrapping_sub iter.iter.end 1#usize
      have hi : i.val = n + 1 := by
        dsimp [i]
        rw [wrapping_sub_one_val _ hend_pos]
        omega
      have hi_pos : 1 ≤ i.val := by omega
      have hpidx : (Usize.wrapping_sub i 1#usize).val = n := by
        rw [wrapping_sub_one_val _ (by omega)]
        omega
      have hp : px.val[(Usize.wrapping_sub i 1#usize).val]? =
          some (encodeBase (g n)) := by
        rw [hpidx]
        exact hpx n (by omega)
      have hv : xs.val[i.val]? = some (encodeBase (f (n + 1))) := by
        rw [hi]
        exact hxs (n + 1) (by omega) (by omega)
      have ho : i.val < ox.length := by simpa only [hi] using hlen
      have hbody := body2_step xs px ox iter x (g n) (f (n + 1))
        hstep hp hv ho
      let iter1 : ReverseRange :=
        ⟨{iter.iter with «end» := Usize.wrapping_sub iter.iter.end 1#usize}⟩
      have hstart1 : iter1.iter.start.val = 1 := by
        simpa [iter1] using hstart
      have hend1 : iter1.iter.end.val = n + 1 := by
        dsimp [iter1]
        rw [wrapping_sub_one_val _ hend_pos]
        omega
      have hxs1 : ∀ j, 1 ≤ j → j ≤ n →
          xs.val[j]? = some (encodeBase (f j)) := by
        intro j hj1 hjn
        exact hxs j hj1 (by omega)
      have hpx1 : ∀ j, j < n →
          px.val[j]? = some (encodeBase (g j)) := by
        intro j hj
        exact hpx j (by omega)
      let ox1 := setNat ox (n + 1) (encodeBase (g n * x))
      have hlen1 : n < ox1.length := by
        simp [ox1, setNat_length]
        omega
      have hrec := ih iter1 (x * f (n + 1)) ox1
        hstart1 hend1 hxs1 hpx1 hlen1
      have hset : ox1 = ox.set i (encodeBase (g n * x)) := by
        dsimp [ox1]
        exact setNat_eq_vec_set ox (n + 1) _ i (by simpa only [hi])
      rw [batch_loop2, loop.eq_def]
      rw [hbody]
      simp only [bind_tc_ok]
      rw [← hset]
      simpa [batch_loop2, reverseModel] using hrec

theorem batch_loop3_body_eq_loop2_body (ys : Slice U32) (py oy : VecU32)
    (iter : ReverseRange) (iy : U32) :
    batch_loop3.body ys py iter iy oy = batch_loop2.body ys py iter iy oy := by
  rfl

theorem batch_loop3_eq_batch_loop2 (iter : ReverseRange)
    (ys : Slice U32) (py : VecU32) (iy : U32) (oy : VecU32) :
    batch_loop3 iter ys py iy oy = batch_loop2 iter ys py iy oy := by
  rfl

#print axioms setNat_eq_vec_set
#print axioms setNat_length
#print axioms batch_loop2_reverseModel
#print axioms batch_loop3_body_eq_loop2_body
#print axioms batch_loop3_eq_batch_loop2

end
end AspisV8R19.R311BatchReverseLoopScratch
