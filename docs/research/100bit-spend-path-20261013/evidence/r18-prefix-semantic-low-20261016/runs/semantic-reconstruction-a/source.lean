import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeDrop

/-! Reconstruction of a list from all of its consecutive fixed-width slices. -/
set_option autoImplicit false

namespace AspisR1.FixedWidthReconstruction

theorem slices_flatten {B : Type} (bytes : List B) (k n : Nat)
    (hlen : bytes.length = n * k) :
    ((List.ofFn (fun i : Fin n => (bytes.drop (k * i.val)).take k)).flatten) = bytes := by
  cases n with
  | zero =>
      simp only [Nat.zero_mul] at hlen
      cases bytes with
      | nil => rfl
      | cons b bs => simp at hlen
  | succ n =>
      cases k with
      | zero =>
          simp only [Nat.mul_zero] at hlen
          cases bytes with
          | nil => simp
          | cons b bs => simp at hlen
      | succ k =>
          classical
          let N := (n + 1) * (k + 1)
          let f : Fin N → B := fun j => bytes.get ⟨j.val, by
            dsimp [N]
            omega⟩
          have hN : bytes.length = N := by
            dsimp [N]
            simpa [Nat.succ_eq_add_one] using hlen
          have hblock (i : Fin (n + 1)) :
              (bytes.drop ((k + 1) * i.val)).take (k + 1) =
                List.ofFn (fun j : Fin (k + 1) =>
                  f ⟨(k + 1) * i.val + j.val, by
                    dsimp [N]
                    have hi : i.val + 1 ≤ n + 1 := Nat.succ_le_of_lt i.isLt
                    have hj : j.val < k + 1 := j.isLt
                    have hwindow : (k + 1) * i.val + (k + 1) ≤ (n + 1) * (k + 1) := by
                      calc
                        (k + 1) * i.val + (k + 1) = i.val * (k + 1) + (k + 1) := by rw [Nat.mul_comm]
                        _ = (i.val + 1) * (k + 1) := by rw [Nat.add_mul, Nat.one_mul]
                        _ ≤ (n + 1) * (k + 1) := Nat.mul_le_mul_right _ hi
                    omega⟩) := by
            apply List.ext_getElem
            · have hi : i.val + 1 ≤ n + 1 := Nat.succ_le_of_lt i.isLt
              have hwindow : (k + 1) * i.val + (k + 1) ≤ (n + 1) * (k + 1) := by
                calc
                  (k + 1) * i.val + (k + 1) = i.val * (k + 1) + (k + 1) := by rw [Nat.mul_comm]
                  _ = (i.val + 1) * (k + 1) := by rw [Nat.add_mul, Nat.one_mul]
                  _ ≤ (n + 1) * (k + 1) := Nat.mul_le_mul_right _ hi
              simp only [List.length_take, List.length_drop, List.length_ofFn]
              omega
            · intro j hj₁ hj₂
              simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
              simp [f]
          have hblocks :
              List.ofFn (fun i : Fin (n + 1) => (bytes.drop ((k + 1) * i.val)).take (k + 1)) =
                List.ofFn (fun i : Fin (n + 1) =>
                  List.ofFn (fun j : Fin (k + 1) =>
                    f ⟨(k + 1) * i.val + j.val, by
                      dsimp [N]
                      have hi : i.val + 1 ≤ n + 1 := Nat.succ_le_of_lt i.isLt
                      have hj : j.val < k + 1 := j.isLt
                      have hwindow : (k + 1) * i.val + (k + 1) ≤ (n + 1) * (k + 1) := by
                        calc
                          (k + 1) * i.val + (k + 1) = i.val * (k + 1) + (k + 1) := by rw [Nat.mul_comm]
                          _ = (i.val + 1) * (k + 1) := by rw [Nat.add_mul, Nat.one_mul]
                          _ ≤ (n + 1) * (k + 1) := Nat.mul_le_mul_right _ hi
                      omega⟩)) := by
            apply congrArg List.ofFn
            funext i
            exact hblock i
          calc
            (List.ofFn (fun i : Fin (n + 1) => (bytes.drop ((k + 1) * i.val)).take (k + 1))).flatten =
                (List.ofFn (fun i : Fin (n + 1) =>
                  List.ofFn (fun j : Fin (k + 1) =>
                    f ⟨(k + 1) * i.val + j.val, by
                      dsimp [N]
                      have hi : i.val + 1 ≤ n + 1 := Nat.succ_le_of_lt i.isLt
                      have hj : j.val < k + 1 := j.isLt
                      have hwindow : (k + 1) * i.val + (k + 1) ≤ (n + 1) * (k + 1) := by
                        calc
                          (k + 1) * i.val + (k + 1) = i.val * (k + 1) + (k + 1) := by rw [Nat.mul_comm]
                          _ = (i.val + 1) * (k + 1) := by rw [Nat.add_mul, Nat.one_mul]
                          _ ≤ (n + 1) * (k + 1) := Nat.mul_le_mul_right _ hi
                      omega⟩))).flatten := by rw [hblocks]
            _ = List.ofFn f := by simpa [Nat.mul_comm] using (List.ofFn_mul f).symm
            _ = bytes := by
              apply List.ext_getElem
              · simp [hN, N, Nat.mul_add, Nat.mul_one]
                omega
              · intro i hi₁ hi₂
                simp only [List.getElem_ofFn]
                simp [f, hN]

#print axioms slices_flatten

end AspisR1.FixedWidthReconstruction
