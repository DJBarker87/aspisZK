import AspisV8R19.SelectorGather

/-! Arithmetic leaves for R58. Registry enumeration and Rust correspondence
are separate source checks, not premises silently supplied by this file. -/
set_option autoImplicit false
namespace AspisV8R19.TagBase

theorem shift_endpoint {R : Type*} [CommRing R] (s b d p : R) :
    s * ((b+d)+p) = s * (d+(p+b)) := by ring

theorem shift_sum {R : Type*} [CommRing R] (xs : List (R × R × R)) (b : R) :
    (xs.map (fun x => x.1 * ((b+x.2.1)+x.2.2))).sum =
    (xs.map (fun x => x.1 * (x.2.1+(x.2.2+b)))).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simpa only [List.map_cons,List.sum_cons,shift_endpoint,ih]

theorem tag_subtraction (d : Nat) : (1124073472+d)-1124073472 = d := by omega

theorem product_bound (x d : Nat) (hx : x < 2^32) (hd : d ≤ 135) :
    x*d ≤ (2^32-1)*135 := by
  exact Nat.mul_le_mul (by omega) hd

theorem sum_bound (xs : List Nat) (h : ∀ x ∈ xs, x ≤ (2^32-1)*135) :
    xs.sum ≤ xs.length * ((2^32-1)*135) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun v hv => h v (List.mem_cons_of_mem x hv))
      simp only [List.sum_cons,List.length_cons]
      omega

theorem accumulator_fits (xs : List Nat) (hlen : xs.length ≤ 272)
    (h : ∀ x ∈ xs, x ≤ (2^32-1)*135) : xs.sum < 2^48 ∧ xs.sum < 2^64 := by
  have hs := sum_bound xs h
  omega

theorem every_prefix_fits (xs ys : List Nat) (hlen : (xs++ys).length ≤ 272)
    (h : ∀ x ∈ xs++ys, x ≤ (2^32-1)*135) : xs.sum < 2^64 := by
  have hs := accumulator_fits (xs++ys) hlen h
  simp only [List.sum_append] at hs
  omega

theorem delayed_reduction (xs : List Nat) :
    SelectorGather.canonicalSum xs = xs.sum % SelectorGather.p :=
  SelectorGather.canonicalSum_eq xs

#print axioms shift_endpoint
#print axioms shift_sum
#print axioms tag_subtraction
#print axioms product_bound
#print axioms sum_bound
#print axioms accumulator_fits
#print axioms every_prefix_fits
#print axioms delayed_reduction
end AspisV8R19.TagBase
