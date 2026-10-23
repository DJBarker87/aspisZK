import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs
set_option autoImplicit false
namespace AspisS2SdkAliasPartition

/-- Canonical first-occurrence object index for three SDK handles. This encodes
identity only; it does not replace any account metadata, bytes or heap state. -/
def slot {H : Type} [DecidableEq H] (handles : Fin 3 → H) (i : Fin 3) : Fin 3 :=
  if handles i=handles 0 then 0 else if handles i=handles 1 then 1 else 2

/-- Every alias pattern of three handles has an exact three-slot encoding.
In particular, distinct keys do not imply distinct data/lamport handles. -/
theorem slot_eq_iff {H : Type} [DecidableEq H] (handles : Fin 3 → H)
    (i j : Fin 3) : slot handles i=slot handles j ↔ handles i=handles j := by
  fin_cases i <;> fin_cases j <;> unfold slot <;> split_ifs <;> simp_all

theorem representative {H : Type} [DecidableEq H] (handles : Fin 3 → H)
    (i : Fin 3) : handles (slot handles i)=handles i := by
  fin_cases i <;> unfold slot <;> split_ifs <;> simp_all

/-- Data and lamport identities can be represented independently while keeping
both exact alias relations. No relation between those two heaps is assumed. -/
theorem independent_heaps {D L : Type} [DecidableEq D] [DecidableEq L]
    (data : Fin 3 → D) (lamports : Fin 3 → L) :
    ∃ dataSlots lamportSlots : Fin 3 → Fin 3,
      (∀ i j,dataSlots i=dataSlots j ↔ data i=data j) ∧
      (∀ i j,lamportSlots i=lamportSlots j ↔ lamports i=lamports j) ∧
      (∀ i,data (dataSlots i)=data i) ∧
      (∀ i,lamports (lamportSlots i)=lamports i) := by
  exact ⟨slot data,slot lamports,slot_eq_iff data,slot_eq_iff lamports,
    representative data,representative lamports⟩

#print axioms slot_eq_iff
#print axioms representative
#print axioms independent_heaps
end AspisS2SdkAliasPartition
