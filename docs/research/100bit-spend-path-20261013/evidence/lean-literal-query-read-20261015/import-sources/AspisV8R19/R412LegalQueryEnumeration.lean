import AspisV8R19.Q22SamplerInvariants
import Mathlib.Logic.Equiv.Fintype

/-!
Finite support for the mechanically bounded Q22 result type. This draft is
uncompiled. It uses only the result-validity facts already proved by
Q22SamplerInvariants; it says nothing about probabilities or sampler
execution.
-/
set_option autoImplicit false
namespace AspisV8R19.R412LegalQueryEnumeration

open scoped BigOperators
open Q22SamplerInvariants

abbrev LegalQuery := {f : Fin 22 → Fin (2^18) // Function.Injective f}

def enumQuery (u : LegalQuery) : List Nat :=
  List.ofFn (fun i : Fin 22 => (u.1 i).val)

theorem enumQuery_injective : Function.Injective enumQuery := by
  intro u v huv
  apply Subtype.ext
  funext i
  apply Fin.ext
  have hfg := List.ofFn_injective huv
  exact congrFun hfg i

/-- Convert a bounded, length-22 list to its coordinate function. -/
def listQuery (xs : List Nat) (hlen : xs.length = 22)
    (hbound : ∀ x ∈ xs, x < 262144) : Fin 22 → Fin (2^18) :=
  fun i => ⟨xs.get ⟨i.val, by omega⟩, by
    have hm : xs.get ⟨i.val, by omega⟩ ∈ xs := List.get_mem xs _
    have hb := hbound _ hm
    exact hb⟩

theorem listQuery_injective (xs : List Nat) (hlen : xs.length = 22)
    (hbound : ∀ x ∈ xs, x < 262144) (hnodup : xs.Nodup) :
    Function.Injective (listQuery xs hlen hbound) := by
  intro i j hij
  apply Fin.ext
  have hget : xs.get ⟨i.val, by omega⟩ = xs.get ⟨j.val, by omega⟩ :=
    congrArg Fin.val hij
  have hidx : (⟨i.val, by omega⟩ : Fin xs.length) = ⟨j.val, by omega⟩ :=
    (List.nodup_iff_injective_get.mp hnodup) hget
  exact congrArg (fun k : Fin xs.length => k.val) hidx

def legalOfList (xs : List Nat) (hnodup : xs.Nodup) (hlen : xs.length = 22)
    (hbound : ∀ x ∈ xs, x < 262144) : LegalQuery :=
  ⟨listQuery xs hlen hbound, listQuery_injective xs hlen hbound hnodup⟩

theorem enum_legalOfList (xs : List Nat) (hnodup : xs.Nodup)
    (hlen : xs.length = 22) (hbound : ∀ x ∈ xs, x < 262144) :
    enumQuery (legalOfList xs hnodup hlen hbound) = xs := by
  apply List.ext_getElem
  · simpa only [enumQuery, List.length_ofFn] using hlen.symm
  · intro i hi hj
    simp only [enumQuery, List.getElem_ofFn, legalOfList, listQuery, List.get_eq_getElem]

theorem existsUnique_enumQuery (xs : List Nat) (hnodup : xs.Nodup)
    (hlen : xs.length = 22) (hbound : ∀ x ∈ xs, x < 262144) :
    ∃! u : LegalQuery, enumQuery u = xs := by
  refine ⟨legalOfList xs hnodup hlen hbound, enum_legalOfList xs hnodup hlen hbound, ?_⟩
  intro v hv
  apply enumQuery_injective
  calc
    enumQuery v = xs := hv
    _ = enumQuery (legalOfList xs hnodup hlen hbound) :=
      (enum_legalOfList xs hnodup hlen hbound).symm

theorem test_eq_legal_sum
    (r : Except Nat (List Nat))
    (hr : Q22SamplerInvariants.ResultValid r)
    (test : Except Nat (List Nat) → ℚ)
    (herr : ∀ n, test (.error n) = 0) :
    test r = ∑ u : LegalQuery,
      if r = .ok (enumQuery u) then test (.ok (enumQuery u)) else 0 := by
  classical
  cases r with
  | error n =>
      simp [herr]
  | ok xs =>
      rcases hr with ⟨hnodup, hlen, hbound⟩
      obtain ⟨u, hu, _⟩ := existsUnique_enumQuery xs hnodup hlen hbound
      rw [Finset.sum_eq_single u]
      · simp [hu]
      · intro v _ hv
        have hne : xs ≠ enumQuery v := by
          intro heq
          apply hv
          apply enumQuery_injective
          calc
            enumQuery v = xs := heq.symm
            _ = enumQuery u := hu.symm
        simp [hne]
      · simp

#print axioms enumQuery_injective
#print axioms listQuery_injective
#print axioms enum_legalOfList
#print axioms existsUnique_enumQuery
#print axioms test_eq_legal_sum

end AspisV8R19.R412LegalQueryEnumeration
