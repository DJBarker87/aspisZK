import AspisV8R17.RawReducerNat

/-!
Natural-number invariants for the retained CU-saving implementations.
These results prove modular equality AND the bounds needed before interpreting
the natural operations as checked u64 operations. Source execution bridges are
separate: this file does not assume an optimized kernel equals its reference.
-/
set_option autoImplicit false
namespace AspisR1.CuSavingsResidues
open AspisV8R17.RawReducer

abbrev ProductMax : Nat := (P - 1) * (P - 1)
abbrev FoldBound : Nat := 2^34

theorem canonical_product_bound (a b : Nat) (ha : a < P) (hb : b < P) :
    a*b ≤ ProductMax :=
  Nat.mul_le_mul (by omega) (by omega)

theorem fold_mod (x : Nat) : foldBits x % P = x % P := by
  rw [foldBits_eq_fold31, fold31_mod]

theorem fold_bound (x : Nat) (hx : x < 2^64) : foldBits x < FoldBound := by
  have h := first_fold_lt x hx
  change foldBits x < 17179869184
  omega

/-- The retained residue plus FOUR maximal products still fits a u64. -/
theorem residue_four_products_fit (raw total : Nat)
    (hr : raw < FoldBound) (ht : total ≤ 4*ProductMax) :
    raw + total < 2^64 := by
  change raw < 17179869184 at hr
  change total ≤ 18446744039349813264 at ht
  change raw + total < 18446744073709551616
  omega

theorem sum_le_length_mul (xs : List Nat) (bound : Nat)
    (h : ∀ x ∈ xs, x ≤ bound) : xs.sum ≤ xs.length * bound := by
  induction xs with
  | nil => simp only [List.sum_nil, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons x xs ih =>
    have hx := h x (by simp only [List.mem_cons, true_or, eq_self])
    have hs := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem four_products_fit (xs : List Nat) (hn : xs.length ≤ 4)
    (h : ∀ x ∈ xs, x ≤ ProductMax) : xs.sum < 2^64 := by
  have hs := sum_le_length_mul xs ProductMax h
  have hm := Nat.mul_le_mul_right ProductMax hn
  have hsum : xs.sum ≤ 4*ProductMax := Nat.le_trans hs hm
  have hf := residue_four_products_fit 0 xs.sum (by decide) hsum
  simpa only [Nat.zero_add] using hf

/-- Optimized base-dot limb: fold each group, then reduce only once. -/
def delayedDot (batches : List (List Nat)) : Nat :=
  rawReduceU64 (batches.map (fun xs => foldBits xs.sum)).sum

theorem folded_batches_bound (batches : List (List Nat))
    (hn : batches.length ≤ 7)
    (h : ∀ xs ∈ batches, xs.length ≤ 4 ∧ ∀ x ∈ xs, x ≤ ProductMax) :
    (batches.map (fun xs => foldBits xs.sum)).sum < 2^37 := by
  have hs := sum_le_length_mul (batches.map (fun xs => foldBits xs.sum))
    (FoldBound - 1) (by
      intro x hx
      obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp hx
      have hb := h xs hxs
      have hf := fold_bound xs.sum (four_products_fit xs hb.1 hb.2)
      omega)
  simp only [List.length_map] at hs
  have hm := Nat.mul_le_mul_right (FoldBound - 1) hn
  change (batches.map (fun xs => foldBits xs.sum)).sum < 137438953472
  change batches.length * 17179869183 ≤ 120259084281 at hm
  change (batches.map (fun xs => foldBits xs.sum)).sum ≤
    batches.length * 17179869183 at hs
  omega

theorem folded_batches_mod (batches : List (List Nat)) :
    (batches.map (fun xs => foldBits xs.sum)).sum % P =
      (batches.map List.sum).sum % P := by
  induction batches with
  | nil => rfl
  | cons xs batches ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Nat.add_mod, fold_mod, ih, ← Nat.add_mod]

theorem delayedDot_eq_reference (batches : List (List Nat))
    (hn : batches.length ≤ 7)
    (h : ∀ xs ∈ batches, xs.length ≤ 4 ∧ ∀ x ∈ xs, x ≤ ProductMax) :
    delayedDot batches = (batches.map List.sum).sum % P := by
  unfold delayedDot
  rw [rawReduceU64_eq_mod_nat _ (by
    have hb := folded_batches_bound batches hn h
    have hp : (2:Nat)^37 < 2^64 := by decide
    omega), folded_batches_mod]

/-- The bound tracks the number of unflushed terms, rather than assuming
    that the accumulator is canonical between queries. -/
def RhoBound (raw count : Nat) : Prop :=
  raw < FoldBound + (count % 4) * ProductMax

def rhoStep (raw count product : Nat) : Nat :=
  if count % 4 = 3 then foldBits (raw + product) else raw + product

theorem rho_add_fits (raw count product : Nat) (hr : RhoBound raw count)
    (hp : product ≤ ProductMax) : raw + product < 2^64 := by
  have hc : count % 4 < 4 := Nat.mod_lt count (by decide)
  have hm := Nat.mul_le_mul_right ProductMax (show count % 4 ≤ 3 by omega)
  unfold RhoBound at hr
  change raw < 17179869184 + count % 4 * 4611686009837453316 at hr
  change product ≤ 4611686009837453316 at hp
  change count % 4 * 4611686009837453316 ≤ 13835058029512359948 at hm
  change raw + product < 18446744073709551616
  omega

theorem rhoStep_bound (raw count product : Nat) (hr : RhoBound raw count)
    (hp : product ≤ ProductMax) : RhoBound (rhoStep raw count product) (count+1) := by
  unfold rhoStep
  split
  · rename_i hc
    have hf := fold_bound (raw+product) (rho_add_fits raw count product hr hp)
    have hz : (count+1)%4 = 0 := by omega
    simpa only [RhoBound, hz, Nat.zero_mul, Nat.add_zero] using hf
  · rename_i hc
    have hn : (count+1)%4 = count%4+1 := by omega
    unfold RhoBound at *
    rw [hn, Nat.add_mul, Nat.one_mul]
    omega

theorem rhoStep_mod (raw count product : Nat) :
    rhoStep raw count product % P = (raw + product) % P := by
  unfold rhoStep
  split
  · exact fold_mod _
  · rfl

def rhoRun (raw count : Nat) (products : List Nat) : Nat :=
  match products with
  | [] => raw
  | p :: ps => rhoRun (rhoStep raw count p) (count+1) ps

theorem rhoRun_invariant (products : List Nat) (raw count : Nat)
    (hr : RhoBound raw count) (hp : ∀ p ∈ products, p ≤ ProductMax) :
    RhoBound (rhoRun raw count products) (count + products.length) ∧
    rhoRun raw count products % P = (raw + products.sum) % P := by
  induction products generalizing raw count with
  | nil =>
    simp only [rhoRun, List.length_nil, List.sum_nil, Nat.add_zero]
    exact ⟨hr, rfl⟩
  | cons p ps ih =>
    have hpb := hp p (by simp only [List.mem_cons, true_or, eq_self])
    obtain ⟨hb, hm⟩ := ih (rhoStep raw count p) (count+1)
      (rhoStep_bound raw count p hr hpb)
      (fun q hq => hp q (List.mem_cons_of_mem p hq))
    constructor
    · simpa only [rhoRun, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hb
    · simp only [rhoRun, List.sum_cons]
      rw [hm, Nat.add_mod, rhoStep_mod, ← Nat.add_mod, Nat.add_assoc]

theorem rhoRun_finish_eq_reference (products : List Nat) (initial : Nat)
    (hi : initial < P) (hp : ∀ p ∈ products, p ≤ ProductMax) :
    rawReduceU64 (rhoRun initial 0 products) = (initial + products.sum) % P := by
  have hr : RhoBound initial 0 := by
    simp only [RhoBound, Nat.zero_mod, Nat.zero_mul, Nat.add_zero]
    change initial < 17179869184
    change initial < 2147483647 at hi
    omega
  obtain ⟨hb, hm⟩ := rhoRun_invariant products initial 0 hr hp
  have hfit := rho_add_fits (rhoRun initial 0 products) products.length 0
    (by simpa only [Nat.zero_add] using hb) (by omega)
  rw [Nat.add_zero] at hfit
  rw [rawReduceU64_eq_mod_nat _ hfit, hm]

#print axioms canonical_product_bound
#print axioms residue_four_products_fit
#print axioms delayedDot_eq_reference
#print axioms rho_add_fits
#print axioms rhoStep_bound
#print axioms rhoRun_invariant
#print axioms rhoRun_finish_eq_reference
end AspisR1.CuSavingsResidues
