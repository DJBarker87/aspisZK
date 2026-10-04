import Mathlib.Data.List.Basic

/-! Source-grammar draft with focused imports. -/
namespace AspisV8PairedCommitment

abbrev Byte := Fin 256

def leafInput (tag : Byte) (value salt : List Byte) : List Byte :=
  16 :: tag :: (value ++ salt)

def parentInput (left right : List Byte) : List Byte :=
  17 :: (left ++ right)

theorem distinct_tree_tags_distinct_inputs
    {t1 t2 : Byte} (different : t1 ≠ t2)
    (v1 v2 salt : List Byte) :
    leafInput t1 v1 salt ≠ leafInput t2 v2 salt := by
  intro equal
  have tails := (List.cons.inj equal).2
  exact different (List.cons.inj tails).1

theorem literal_v7_pair_inputs_distinct (v1 v2 salt : List Byte) :
    leafInput 113 v1 salt ≠ leafInput 241 v2 salt := by
  apply distinct_tree_tags_distinct_inputs
  decide

theorem parent_input_length (left right : List Byte)
    (hl : left.length = 26) (hr : right.length = 26) :
    (parentInput left right).length = 53 := by
  simp [parentInput, hl, hr]

theorem leaf_input_length (tag : Byte) (value salt : List Byte)
    (hs : salt.length = 32) :
    (leafInput tag value salt).length = value.length + 34 := by
  simp [leafInput, hs]

/-- Literal parent calls cannot address a deferred leaf input. This rules
out this specific query class, not unrelated transcript/hashv grammars. -/
theorem parent_input_ne_leaf_input (left right value salt : List Byte) (tag : Byte) :
    parentInput left right ≠ leafInput tag value salt := by
  intro equal
  have impossible : (17 : Byte) = 16 := (List.cons.inj equal).1
  exact (by decide : (17 : Byte) ≠ 16) impossible

#print axioms parent_input_ne_leaf_input
#print axioms literal_v7_pair_inputs_distinct
end AspisV8PairedCommitment
