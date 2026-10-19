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
      simp at hlen
      simp [hlen]
  | succ n =>
      cases k with
      | zero =>
          simp at hlen
          simp [hlen]
      | succ k =>
          -- Use `ofFn_mul'` to expose the consecutive `Fin (k+1)` slices,
          -- then identify each slice using `getElem_drop` and `take`.
          classical
          let N := (n + 1) * (k + 1)
          let f : Fin N → B := fun j => bytes.get ⟨j.val, by
            dsimp [N]
            omega⟩
          have hN : bytes.length = N := by
            dsimp [N]
            simpa [Nat.succ_eq_add_one] using hlen
          have hf : List.ofFn f = bytes := by
            apply List.ext_getElem
            · simp [hN]
            · intro i hi₁ hi₂
              simp only [List.getElem_ofFn]
              simp [f, hN]
          rw [← hf, List.ofFn_mul']
          simp [f, N, List.getElem_drop, List.getElem_take, hN,
            Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

#print axioms slices_flatten

end AspisR1.FixedWidthReconstruction
