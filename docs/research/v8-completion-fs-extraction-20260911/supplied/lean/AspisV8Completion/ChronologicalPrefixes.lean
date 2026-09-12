/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import Mathlib
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Completion.ChronologicalPrefixes
variable {A B : Type*}

/-- An actual prefix rather than arbitrary set inclusion in a log. -/
def PrefixOf (prefix whole : List A) : Prop := ∃ tail, whole = prefix ++ tail

theorem prefix_refl (xs : List A) : PrefixOf xs xs := ⟨[], by simp⟩

theorem prefix_trans {a b c : List A} (ab : PrefixOf a b) (bc : PrefixOf b c) :
    PrefixOf a c := by
  obtain ⟨x,rfl⟩ := ab
  obtain ⟨y,rfl⟩ := bc
  exact ⟨x++y, by simp [List.append_assoc]⟩

theorem take_is_prefix (n : Nat) (xs : List A) : PrefixOf (xs.take n) xs := by
  exact ⟨xs.drop n, (List.take_append_drop n xs).symm⟩

/-- True causal construction depends on the prefix, not a completed body. -/
def atCut (f : List A → B) (cut : Nat) (history : List A) : B := f (history.take cut)

theorem cut_noninterference (f : List A → B) (cut : Nat) (left right : List A)
    (samePrefix : left.take cut = right.take cut) :
    atCut f cut left = atCut f cut right := congrArg f samePrefix

/-- Pairwise equality factors through the cut. The producer f must be a
source-derived algorithm, not a choice selected after seeing the conclusion. -/
theorem extension_invariant (f : List A → B) (prefix tail : List A) :
    atCut f prefix.length (prefix ++ tail) = f prefix := by
  simp [atCut]

structure PhaseCuts (history : List A) where
  c1 : Nat
  lambda : Nat
  c2 : Nat
  ood : Nat
  c1Before : c1 ≤ lambda
  afterLambda : lambda < c2
  c2Before : c2 ≤ ood
  inBounds : ood < history.length

def PhaseCuts.early {history : List A} (cuts : PhaseCuts history) : List A := history.take cuts.c1

def PhaseCuts.second {history : List A} (cuts : PhaseCuts history) : List A := history.take cuts.c2

/-- Cut arithmetic only. Identifying the real lambda/OOD calls is a separate
source proof, never inferred merely from field names. -/
theorem phase_cut_order {history : List A} (cuts : PhaseCuts history) :
    cuts.c1 < cuts.c2 ∧ cuts.c2 < history.length := by
  constructor <;> omega

#print axioms cut_noninterference
#print axioms extension_invariant
end AspisV8Completion.ChronologicalPrefixes
