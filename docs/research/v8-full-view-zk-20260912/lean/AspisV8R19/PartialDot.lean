import AspisV8R19.PartialProduct

/-! R59 four-accumulator arithmetic boundary. The unchanged guarded raw
product and Rust loop remain separately source-checked, not extracted here. -/
set_option autoImplicit false
namespace AspisV8R19.PartialDot
open PartialProduct

theorem word_fold_bound (x : Nat) (hx : x < 2^64) : foldOnce x < 2^34 := by
  have hm := Nat.mod_lt x (show 0 < p+1 by decide)
  have hd : x/(p+1) < 2^33 := by
    apply (Nat.div_lt_iff_lt_mul (show 0 < p+1 by decide)).mpr
    simpa [p] using hx
  unfold foldOnce
  simp only [p] at *
  omega

theorem folded_sum_bound (xs : List Nat) (h : ∀ x ∈ xs, x < 2^64) :
    (xs.map foldOnce).sum ≤ xs.length * (2^34-1) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := word_fold_bound x (h x (by simp))
      have ht := ih (fun v hv => h v (List.mem_cons_of_mem x hv))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      omega

theorem accumulator_fits (xs : List Nat) (hlen : xs.length ≤ 4096)
    (h : ∀ x ∈ xs, x < 2^64) :
    (xs.map foldOnce).sum < 2^46 ∧ (xs.map foldOnce).sum < 2^64 := by
  have hs := folded_sum_bound xs h
  omega

theorem every_prefix_fits (xs ys : List Nat) (hlen : (xs++ys).length ≤ 4096)
    (h : ∀ x ∈ xs++ys, x < 2^64) : (xs.map foldOnce).sum < 2^64 := by
  have hs := accumulator_fits (xs++ys) hlen h
  simp only [List.map_append,List.sum_append] at hs
  omega

theorem delayed_output_reduction (xs : List Nat) :
    (xs.map foldOnce).sum % p = xs.sum % p := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons,List.sum_cons]
      rw [Nat.add_mod,partial_mod,ih,← Nat.add_mod]

theorem canonical_output (xs : List Nat) : (xs.map foldOnce).sum % p < p :=
  Nat.mod_lt _ (by decide)

theorem third_coordinate_bounds (ag ce bh df : Nat)
    (hag : ag < p*p) (hce : ce < p*p) (hbh : bh < p*p) (hdf : df < p*p) :
    ag+ce+2*p*p < 2^64 ∧ bh ≤ ag+ce+2*p*p ∧ df ≤ ag+ce+2*p*p-bh := by
  simp only [p] at *
  omega

theorem fourth_coordinate_bound (ah bg cf de : Nat)
    (hah : ah < p*p) (hbg : bg < p*p) (hcf : cf < p*p) (hde : de < p*p) :
    ah+bg+cf+de < 2^64 := by
  simp only [p] at *
  omega

#print axioms word_fold_bound
#print axioms folded_sum_bound
#print axioms accumulator_fits
#print axioms every_prefix_fits
#print axioms delayed_output_reduction
#print axioms canonical_output
#print axioms third_coordinate_bounds
#print axioms fourth_coordinate_bound
end AspisV8R19.PartialDot
