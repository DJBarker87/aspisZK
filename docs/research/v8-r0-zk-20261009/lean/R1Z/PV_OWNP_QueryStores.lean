import R1Z.PV_OWNP_PointArray
set_option autoImplicit false
namespace R1Z.PV_OWNP_QueryStores
open Aeneas Aeneas.Std PV_OWNK_TowerCanon
open PV_OWNO_PointStores

/-- Each completed round writes precisely its own challenge coordinate. -/
def prior (rank : Fin 10 → List U32) (round : Fin 10) : List Write :=
 (List.finRange round.val).map fun i =>
  .challenge ⟨i.val, Nat.lt_trans i.isLt round.isLt⟩ (rank ⟨i.val, Nat.lt_trans i.isLt round.isLt⟩)

/-- Source round+1+offset, including round9's empty suffix. -/
def suffixIndex (round : Fin 10) (offset : Fin (9-round.val)) : Fin 10 :=
 ⟨round.val+1+offset.val, by have hr := round.isLt; have ho := offset.isLt; omega⟩

def suffix (round : Fin 10) (assignment : Nat) : List Write :=
 (List.finRange (9-round.val)).map fun offset =>
  .boolean (suffixIndex round offset)
   (assignment.testBit (9-round.val-1-offset.val))

/-- Current sample store precedes every assignment's ascending suffix stores. -/
def queryWrites (rank : Fin 10 → List U32) (round : Fin 10)
 (sample : Fin 28) (assignment : Nat) : List Write :=
 prior rank round ++ [.sample round sample] ++ suffix round assignment

def finalWrites (rank : Fin 10 → List U32) : List Write :=
 (List.finRange 10).map fun i => .challenge i (rank i)

def callback (combine : U64 → U32 → U64) (rank : Fin 10 → List U32)
 (round : Fin 10) (sample : Fin 28) (assignment : Nat) : PV_OWNP_PointArray.Point :=
 PV_OWNP_PointArray.run combine (queryWrites rank round sample assignment)

def terminal (combine : U64 → U32 → U64) (rank : Fin 10 → List U32) :
 PV_OWNP_PointArray.Point := PV_OWNP_PointArray.run combine (finalWrites rank)

theorem suffix_bounds (round : Fin 10) (offset : Fin (9-round.val)) :
 round.val < (suffixIndex round offset).val ∧ (suffixIndex round offset).val < 10 := by
 constructor
 · change round.val < round.val+1+offset.val; omega
 · exact (suffixIndex round offset).isLt

theorem query_count (rank : Fin 10 → List U32) (round : Fin 10)
 (sample : Fin 28) (assignment : Nat) :
 (queryWrites rank round sample assignment).length = 10 := by
 simp only [queryWrites,prior,suffix,List.length_append,List.length_map,
  List.length_finRange,List.length_singleton]
 have hr := round.isLt
 omega

theorem terminal_count (rank : Fin 10 → List U32) : (finalWrites rank).length = 10 := by
 simp only [finalWrites,List.length_map,List.length_finRange]

theorem callback_canonical (combine : U64 → U32 → U64)
 (rank : Fin 10 → List U32) (round : Fin 10) (sample : Fin 28) (assignment : Nat) :
 ∀ q ∈ (callback combine rank round sample assignment).val, Canon q :=
 PV_OWNP_PointArray.run_canonical combine _

theorem terminal_canonical (combine : U64 → U32 → U64) (rank : Fin 10 → List U32) :
 ∀ q ∈ (terminal combine rank).val, Canon q := PV_OWNP_PointArray.run_canonical combine _

#print axioms suffix_bounds
#print axioms query_count
#print axioms terminal_count
#print axioms callback_canonical
#print axioms terminal_canonical
end R1Z.PV_OWNP_QueryStores
