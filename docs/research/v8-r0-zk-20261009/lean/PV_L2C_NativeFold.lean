import PV_L2C_M31
set_option autoImplicit false
namespace PV_L2C_NativeFold
open PV_L2C_M31
/-- Sequential native addition fold, after the public active-row filter. -/
def fold : List word → word → word
 | [], s => s
 | x::xs, s => fold xs (add s x)

theorem fold_canonical (xs : List word) (hxs : ∀ x ∈ xs, canonical x)
    (s : word) (hs : canonical s) : canonical (fold xs s) := by
  induction xs generalizing s with
  | nil => exact hs
  | cons x xs ih =>
    exact ih (fun x hx => hxs x (by simp [hx])) (add s x)
      (add_canonical s x hs (hxs x (by simp)))
#print axioms fold_canonical

theorem fold_decode (xs : List word) (hxs : ∀ x ∈ xs, canonical x)
    (s : word) (hs : canonical s) :
    decode (fold xs s)=decode s+(xs.map decode).sum := by
  induction xs generalizing s with
  | nil => simp [fold]
  | cons x xs ih =>
    rw [fold,ih (fun x hx => hxs x (by simp [hx])) (add s x)
      (add_canonical s x hs (hxs x (by simp))),add_decode s x hs (hxs x (by simp))]
    simp [add_assoc]
#print axioms fold_decode

theorem fold_zero_decode (xs : List word) (hxs : ∀ x ∈ xs, canonical x) :
    decode (fold xs 0)=(xs.map decode).sum := by
  rw [fold_decode xs hxs 0 (by unfold canonical p; decide)]
  simp [decode]
#print axioms fold_zero_decode

theorem negate_decode (xs : List word) (hxs : ∀ x ∈ xs, canonical x) :
    canonical (sub 0 (fold xs 0)) ∧
      decode (sub 0 (fold xs 0))=-(xs.map decode).sum := by
  have hz : canonical 0 := by unfold canonical p; decide
  have hc := fold_canonical xs hxs 0 hz
  exact ⟨sub_canonical _ _ hz hc, by rw [sub_decode _ _ hz hc,fold_zero_decode xs hxs]; simp [decode]⟩
#print axioms negate_decode
end PV_L2C_NativeFold
