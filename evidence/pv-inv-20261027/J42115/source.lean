import R1Z.PV_Inv_Interpolation
set_option autoImplicit false
namespace R1Z.PV_Inv_InterpolationLoop
variable {p n : ℕ} [Fact p.Prime]

def loop (i : Fin n) : ZMod p → List (Fin n) → ZMod p
  | d,[] => d
  | d,j::js => loop i (if i=j then d else d*((i.val : ZMod p)-(j.val : ZMod p))) js

theorem preserves (hn : n ≤ p) (i : Fin n) (js : List (Fin n))
    (d : ZMod p) (hd : d ≠ 0) : loop i d js ≠ 0 := by
  induction js generalizing d with
  | nil => exact hd
  | cons j js ih =>
    apply ih
    by_cases h : i=j
    · simpa [h] using hd
    · simp only [h,if_false]
      apply mul_ne_zero hd
      exact sub_ne_zero.mpr (fun he => h (PV_Inv_Interpolation.node_injective hn he))

theorem initialized (hn : n ≤ p) (i : Fin n) (js : List (Fin n)) : loop i (1 : ZMod p) js ≠ 0 :=
  preserves hn i js 1 one_ne_zero

#print axioms preserves
#print axioms initialized
end R1Z.PV_Inv_InterpolationLoop
