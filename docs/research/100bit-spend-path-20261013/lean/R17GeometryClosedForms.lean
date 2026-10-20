import FoldFactoredDomain
import FoldD18Commutation

/-! R17 closed forms at symbolic indices. Literal-byte validation is an
external optimized Rust certificate, never a new Lean axiom. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.R17GeometryClosedForms
open AspisCircleGroupOrder AspisV5FriBitReverse AspisV7ExactOneFoldDomains
open FoldStoredGeometry FoldFactoredDomain

/-- Sequential generation, with the entry emitted before advancing. -/
def walk {G : Type*} [Monoid G] (initial step : G) : Nat → G
  | 0 => initial
  | i + 1 => walk initial step i * step

theorem walk_closed {G : Type*} [Monoid G] (initial step : G) (i : Nat) :
    walk initial step i = initial * step ^ i := by
  induction i with
  | zero => simp only [walk, pow_zero, mul_one]
  | succ i ih => rw [walk, ih, pow_succ, mul_assoc]

/-- The offset/stride closed form is preserved by one generation step. -/
theorem exponent_walk (offset stride : Int) (i : Nat) :
    walk (g ^ offset) (g ^ stride) i = g ^ (offset + stride * (i : Int)) := by
  rw [walk_closed, ← zpow_natCast, ← zpow_mul, ← zpow_add]

theorem tableA_recurrence (i : Nat) :
    tableA i = walk (g ^ (1024 : Int)) (g ^ (2097152 : Int)) (reverseBits 9 i) := by
  exact (exponent_walk 1024 2097152 (reverseBits 9 i)).symm

theorem tableB_recurrence (i : Nat) :
    tableB i = walk (g ^ (0 : Int)) (g ^ (4096 : Int)) (reverseBits 9 i) := by
  simpa only [tableB, zero_add] using (exponent_walk 0 4096 (reverseBits 9 i)).symm

/-- The actual mask and shift select the two 9-bit limbs. -/
theorem lookup_geometry (u : Fin 262144) :
    u.val &&& 511 = u.val % 512 ∧
    u.val >>> 9 = u.val / 512 ∧
    u.val &&& 511 < 512 ∧ u.val >>> 9 < 512 := by
  have hm : u.val &&& 511 = u.val % 512 := Nat.and_two_pow_sub_one_eq_mod u.val 9
  have hs : u.val >>> 9 = u.val / 512 := Nat.shiftRight_eq_div_pow u.val 9
  have hu := u.isLt
  rw [hm, hs]
  omega

/-- Closed forms selected by source lookups equal the existing stored domain. -/
theorem masked_tables_eq_stored (u : Fin 262144) :
    tableA (u.val &&& 511) * tableB (u.val >>> 9) = storedInitialFibrePoint20 u := by
  rw [(lookup_geometry u).1, (lookup_geometry u).2.1,
    factored_fibre, fibre_eq_stored]

/-- Literal natural_index match from core domain.rs, interpreted over Nat. -/
def sourceNatural (i : Fin (4 * 262144)) : Nat :=
  let r := reverseBits 18 (i.val / 4)
  match i.val % 4 with
  | 0 => 2*r
  | 1 => 1048576-1-2*r
  | 2 => 524288+2*r
  | _ => 524288-1-2*r

theorem natural_child (u : Fin 262144) (s : Fin 4) :
    sourceNatural (AspisV5ComponentCConcreteFoldLinearity.childIndex u s) =
      (storedInitialNaturalIndex20
        (AspisV5ComponentCConcreteFoldLinearity.childIndex u s)).val := by
  have hd : (4 * u.val + s.val) / 4 = u.val := by omega
  have hm : (4 * u.val + s.val) % 4 = s.val := by omega
  have cases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by
    have hs := s.isLt
    omega
  rcases cases with h | h | h | h
  · subst s
    rw [storedInitialNaturalIndex20_child_zero]
    simp only [sourceNatural, AspisV5ComponentCConcreteFoldLinearity.childIndex_val,
      hd, hm]
    rfl
  · subst s
    rw [storedInitialNaturalIndex20_child_one]
    simp only [sourceNatural, AspisV5ComponentCConcreteFoldLinearity.childIndex_val,
      hd, hm]
    rfl
  · subst s
    rw [storedInitialNaturalIndex20_child_two]
    simp only [sourceNatural, AspisV5ComponentCConcreteFoldLinearity.childIndex_val,
      hd, hm]
    rfl
  · subst s
    rw [storedInitialNaturalIndex20_child_three]
    simp only [sourceNatural, AspisV5ComponentCConcreteFoldLinearity.childIndex_val,
      hd, hm]
    rfl

theorem natural_eq_stored (i : Fin (4 * 262144)) :
    sourceNatural i = (storedInitialNaturalIndex20 i).val := by
  let u : Fin 262144 := ⟨i.val / 4, by omega⟩
  let s : Fin 4 := ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩
  have hi : i = AspisV5ComponentCConcreteFoldLinearity.childIndex u s := by
    apply Fin.ext
    change i.val = 4 * (i.val / 4) + i.val % 4
    omega
  rw [hi]
  exact natural_child u s

theorem natural_injective : Function.Injective sourceNatural := by
  intro i j h
  apply storedInitialNaturalIndex20_injective
  apply Fin.ext
  exact (natural_eq_stored i).symm.trans (h.trans (natural_eq_stored j))

/-- Exact loop-free source lookup specification; table values stay premises. -/
theorem literal_lookup_to_stored (a b : Nat → C)
    (hA : ∀ i, i < 512 → a i = tableA i)
    (hB : ∀ i, i < 512 → b i = tableB i) (u : Fin 262144) :
    a (u.val &&& 511) * b (u.val >>> 9) = storedInitialFibrePoint20 u := by
  rw [(lookup_geometry u).1, (lookup_geometry u).2.1]
  exact tables_to_stored a b hA hB u

#print axioms walk_closed
#print axioms exponent_walk
#print axioms tableA_recurrence
#print axioms tableB_recurrence
#print axioms lookup_geometry
#print axioms masked_tables_eq_stored
#print axioms natural_child
#print axioms natural_eq_stored
#print axioms natural_injective
#print axioms literal_lookup_to_stored
end AspisR1.R17GeometryClosedForms
