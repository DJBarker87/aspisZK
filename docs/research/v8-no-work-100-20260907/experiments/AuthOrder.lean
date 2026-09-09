import Mathlib.Tactic
import Mathlib.Data.List.Sort

namespace AspisV8.AuthOrder
def base : Nat := 4294967296
def pack (key ordinal : Nat) := key*base+ordinal

theorem packed_decode (key i : Nat) (hi : i<base) :
    pack key i / base=key ∧ pack key i % base=i := by
  dsimp [pack,base] at *; omega
theorem packed_order (a b i j : Nat) (hi : i<base) (hj : j<base) :
    pack a i < pack b j ↔ a<b ∨ (a=b ∧ i<j) := by
  dsimp [pack,base] at *; omega
theorem packed_range (key i : Nat) (hk : key<base) (hi : i<22) :
    pack key i < 2^64 := by dsimp [pack,base] at *; omega
theorem record_bounds (i : Nat) (hi : i<22) : (i+1)*621 ≤ 22*621 := by omega

theorem strict_iff_nodup {A : Type*} (key : A → Nat) (xs : List A)
    (weak : xs.Pairwise (fun a b => key a ≤ key b)) :
    xs.Pairwise (fun a b => key a < key b) ↔ (xs.map key).Nodup := by
  constructor
  · intro h
    exact List.pairwise_map.mpr (h.imp (fun hab => Nat.ne_of_lt hab))
  · intro h
    have hn : xs.Pairwise (fun a b => key a ≠ key b) := List.pairwise_map.mp h
    exact (weak.and hn).imp (fun hab => by omega)

-- Both implementations sort permutations of the same immutable leaf values.
-- Sorted duplicate keys reject on BOTH paths; no uniqueness assumption is
-- imported from the honest prover or from the query sampler.
theorem authentication_congr {A : Type*} (key : A → Nat) (finish : List A → Bool)
    (xs ys : List A) (hp : xs.Perm ys)
    (hx : xs.Pairwise (fun a b => key a ≤ key b))
    (hy : ys.Pairwise (fun a b => key a ≤ key b)) :
    (if xs.Pairwise (fun a b => key a < key b) then finish xs else false) =
    (if ys.Pairwise (fun a b => key a < key b) then finish ys else false) := by
  have hs := (strict_iff_nodup key xs hx).trans
    ((hp.map key).nodup_iff.trans (strict_iff_nodup key ys hy).symm)
  by_cases h : xs.Pairwise (fun a b => key a < key b)
  · have h' := hs.mp h
    have heq : xs=ys := List.Perm.eq_of_pairwise
      (fun a b _ _ hab hba => by omega) h h' hp
    rw [heq]
  · simp only [if_neg h,if_neg (hs.not.mp h)]

#print axioms packed_decode
#print axioms packed_order
#print axioms packed_range
#print axioms record_bounds
#print axioms strict_iff_nodup
#print axioms authentication_congr
end AspisV8.AuthOrder
