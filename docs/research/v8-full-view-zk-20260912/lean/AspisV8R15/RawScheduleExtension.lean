import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic

/-! Universal zero-extension of a two-fibre scalar statistic.

This is deterministic algebra, not a schedule probability or source-wide
privacy theorem. The encoded observation has four scalar slots per fibre,
matching the literal C1 opening layout. No distribution on schedules is used.
-/

set_option autoImplicit false
namespace AspisV8R15
open scoped BigOperators

variable {F : Type*} [CommRing F] {n : ℕ}

def pairStat (a b : ℕ) (left right : Fin 4 → F)
    (encoded : ℕ → Fin 4 → F) : F :=
  (∑ s, left s * encoded a s) + ∑ s, right s * encoded b s

def extendedStat (schedule : Fin n → ℕ) (a b : ℕ)
    (left right : Fin 4 → F) (encoded : ℕ → Fin 4 → F) : F :=
  ∑ i, ∑ s,
    ((if schedule i = a then left s else 0) +
      (if schedule i = b then right s else 0)) * encoded (schedule i) s

/-- Any injective schedule containing the two fibres returns exactly the
original statistic, independent of its length, order or selection method. -/
theorem zero_extension_exact (schedule : Fin n → ℕ)
    (injective : Function.Injective schedule) (a b : ℕ)
    (ia ib : Fin n) (hia : schedule ia = a) (hib : schedule ib = b)
    (left right : Fin 4 → F) (encoded : ℕ → Fin 4 → F) :
    extendedStat schedule a b left right encoded = pairStat a b left right encoded := by
  have ha : ∀ i, schedule i = a ↔ i = ia := by
    intro i
    constructor
    · intro h
      exact injective (h.trans hia.symm)
    · intro h
      exact h ▸ hia
  have hb : ∀ i, schedule i = b ↔ i = ib := by
    intro i
    constructor
    · intro h
      exact injective (h.trans hib.symm)
    · intro h
      exact h ▸ hib
  simp only [extendedStat, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, ha, hb]
  simp [pairStat, hia, hib]

def q46Left (s : Fin 4) : F :=
  match s.val with
  | 0 => 1508290849
  | 1 => 1480589898
  | 2 => 639192798
  | _ => 666893749

def q46Right (s : Fin 4) : F :=
  match s.val with
  | 0 => 2147483646
  | 1 => 0
  | 2 => 1
  | _ => 0

/-- Literal q4/q6 coefficient instance. Authenticating its source mask/target
products is a separate source gate; this theorem universally embeds them. -/
theorem q4_q6_zero_extension (schedule : Fin 22 → ℕ)
    (injective : Function.Injective schedule)
    (i4 i6 : Fin 22) (h4 : schedule i4 = 4) (h6 : schedule i6 = 6)
    (encoded : ℕ → Fin 4 → F) :
    extendedStat schedule 4 6 q46Left q46Right encoded =
      pairStat 4 6 q46Left q46Right encoded :=
  zero_extension_exact schedule injective 4 6 i4 i6 h4 h6 q46Left q46Right encoded

#print axioms zero_extension_exact
#print axioms q4_q6_zero_extension
end AspisV8R15
