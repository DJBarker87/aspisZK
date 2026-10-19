import AspisR1BatchedWeightsExtraction.Funs
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
open AspisR1BatchedWeightsExtraction
namespace BatchedWeightsVecResizeLengthGenericV1

theorem resize_success_length {T : Type} (clone : core.clone.Clone T)
    (base out : alloc.vec.Vec T) (n : Std.Usize) (value : T)
    (h : alloc.vec.Vec.resize clone base n value = .ok out) :
    out.length = n.val := by
  unfold alloc.vec.Vec.resize at h
  split_ifs at h with hlt
  · injection h with hout
    subst out
    simp only [alloc.vec.Vec.length]
    change (List.resize (↑base) n.val value).length = n.val
    simp [List.resize, List.length_append, List.length_take, List.length_replicate,
      Nat.min_eq_left (Nat.le_of_lt hlt), Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)]
  · have hle : List.length (↑base : List T) ≤ n.val := by
      simpa only [alloc.vec.Vec.length] using (Nat.le_of_not_gt hlt)
    cases hclone : clone.clone value with
    | fail e => simp [hclone] at h
    | div => simp [hclone] at h
    | ok cloned =>
      simp only [hclone, bind_tc_ok] at h
      injection h with hout
      subst out
      simp only [alloc.vec.Vec.length]
      change (List.resize (↑base) n.val cloned).length = n.val
      simp [List.resize, List.length_append, List.length_take, List.length_replicate,
        Nat.min_eq_right hle] <;> omega
#print axioms resize_success_length
end BatchedWeightsVecResizeLengthGenericV1
