import Mathlib.Tactic

namespace AspisV8.CopyTagSplit

def p : Nat := 2147483647
def base : Nat := 1124073472
def rotated (s : Nat) : Nat := (s % 128) * 16777216 + s / 128

-- The relation is an equality of natural numbers, before reducing modulo p.
theorem rotate_decomposition (s : Nat) :
    s * 16777216 = rotated s + (s / 128) * p := by
  have h := Nat.mod_add_div s 128
  dsimp [rotated, p]
  omega

theorem split_mod (s d : Nat) :
    (base * s + d) % p = (67 * rotated s + d) % p := by
  have h := rotate_decomposition s
  have hs : base*s+d = (67*rotated s+d)+(67*(s/128))*p := by
    dsimp [base] at *
    nlinarith
  rw [hs, Nat.add_mul_mod_self_right]

-- Literal tags split into one shared prefix and a bounded small offset.
theorem list_split (xs : List (Nat × Nat)) :
    (xs.map (fun ai => ai.1 * (base + ai.2))).sum =
      base * (xs.map Prod.fst).sum + (xs.map (fun ai => ai.1*ai.2)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.map_cons,List.sum_cons,ih]; ring

theorem sum_bound (xs : List Nat) (b : Nat) (hx : ∀ x ∈ xs, x ≤ b) :
    xs.sum ≤ xs.length*b := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := hx a (by simp)
    have hi := ih (by intro x hm; exact hx x (by simp [hm]))
    simp only [List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem accumulators_bound (xs : List (Nat × Nat))
    (hn : xs.length ≤ 272)
    (ha : ∀ x ∈ xs, x.1 < p)
    (hi : ∀ x ∈ xs, x.2 ≤ 135) :
    (xs.map Prod.fst).sum ≤ 584115551712 ∧
    (xs.map (fun x => x.1*x.2)).sum ≤ 78855599481120 := by
  have hs := sum_bound (xs.map Prod.fst) (p-1) (by
    intro a hm; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hm; have hh := ha x hx; omega)
  have hd := sum_bound (xs.map (fun x => x.1*x.2)) ((p-1)*135) (by
    intro a hm; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hm
    exact Nat.mul_le_mul (by have hh := ha x hx; omega) (hi x hx))
  simp only [List.length_map] at hs hd
  have hns := Nat.mul_le_mul_right (p-1) hn
  have hnd := Nat.mul_le_mul_right ((p-1)*135) hn
  norm_num [p] at hs hd hns hnd
  constructor <;> omega

theorem all_prefixes_bound (xs : List (Nat × Nat))
    (hn : xs.length ≤ 272) (ha : ∀ x ∈ xs, x.1 < p)
    (hi : ∀ x ∈ xs, x.2 ≤ 135) (n : Nat) :
    ((xs.take n).map Prod.fst).sum ≤ 584115551712 ∧
    ((xs.take n).map (fun x => x.1*x.2)).sum ≤ 78855599481120 := by
  apply accumulators_bound
  · exact le_trans (by simp) hn
  · intro x hx; exact ha x (List.mem_of_mem_take hx)
  · intro x hx; exact hi x (List.mem_of_mem_take hx)

-- Also bounds the masked left shift, addition, scaling and final addition:
-- they are nonnegative subexpressions of this bounded accumulator.
theorem final_raw_bound (s d : Nat) (hs : s ≤ 584115551712)
    (hd : d ≤ 78855599481120) :
    67 * rotated s + d ≤ 79304104796113 ∧
    67 * rotated s + d < 2^64 := by
  have hm := Nat.mod_lt s (by omega : 0 < 128)
  have hdiv : s/128 ≤ 4563402747 := by omega
  dsimp [rotated]
  constructor <;> omega

theorem source_accumulator_mod (xs : List (Nat × Nat)) :
    (xs.map (fun x => x.1*(base+x.2))).sum % p =
      (67*rotated (xs.map Prod.fst).sum + (xs.map (fun x => x.1*x.2)).sum) % p := by
  rw [list_split,split_mod]

-- Each machine wrapping operation is an ordinary operation at these proven
-- ranges. This is a range/model bridge, not a Rust compiler translation.
theorem wrapping_prefixes_exact (xs : List (Nat × Nat))
    (hn : xs.length ≤ 272) (ha : ∀ x ∈ xs, x.1 < p)
    (hi : ∀ x ∈ xs, x.2 ≤ 135) (n : Nat) :
    ((xs.take n).map Prod.fst).sum % (2^64) = ((xs.take n).map Prod.fst).sum ∧
    ((xs.take n).map (fun x => x.1*x.2)).sum % (2^64) =
      ((xs.take n).map (fun x => x.1*x.2)).sum := by
  have h := all_prefixes_bound xs hn ha hi n
  constructor <;> apply Nat.mod_eq_of_lt <;> omega

theorem wrapping_product_exact (a i : Nat) (ha : a < p) (hi : i ≤ 135) :
    (a*i) % (2^64) = a*i := by
  have h : a*i ≤ (p-1)*135 := Nat.mul_le_mul (by omega) hi
  apply Nat.mod_eq_of_lt
  norm_num [p] at h
  omega

theorem wrapping_final_exact (s d : Nat) (hs : s ≤ 584115551712)
    (hd : d ≤ 78855599481120) :
    (67*rotated s+d) % (2^64) = 67*rotated s+d :=
  Nat.mod_eq_of_lt (final_raw_bound s d hs hd).2

#print axioms rotate_decomposition
#print axioms split_mod
#print axioms list_split
#print axioms accumulators_bound
#print axioms all_prefixes_bound
#print axioms final_raw_bound
#print axioms source_accumulator_mod
#print axioms wrapping_prefixes_exact
#print axioms wrapping_product_exact
#print axioms wrapping_final_exact
end AspisV8.CopyTagSplit
