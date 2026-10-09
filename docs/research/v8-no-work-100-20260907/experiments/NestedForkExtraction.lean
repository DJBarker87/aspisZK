import RegularQueryMoment

/-! A finite, causal two-level forking bound.  This is the exact combinatorial
shape needed after the deterministic four-alpha / twenty-nine-gamma recovery
bridges: if those bridges would construct `X` whenever 29 outer challenges
each admit four inner continuations, then failure of `X` leaves at most 28
unrestricted outer challenges and at most three successful inner challenges
everywhere else.

This file does not assert that verifier acceptance supplies the recovery
predicate, nor does it perform a Fiat--Shamir lift.  The outer and inner
finite means are explicit ideal fresh-challenge experiments. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 300000

namespace AspisV8.NestedForkExtraction
open Finset
open AspisV8.JointImageGame
open AspisV8.RegularQueryMoment.Generic
noncomputable section

variable {Outer Inner : Type*} [DecidableEq Outer] [DecidableEq Inner]

def innerHits (I : Finset Inner) (event : Outer → Inner → Prop)
    (outer : Outer) : Finset Inner := by
  classical
  exact I.filter fun inner => event outer inner

def forkable (O : Finset Outer) (I : Finset Inner)
    (event : Outer → Inner → Prop)
    (needed : Nat) : Finset Outer := by
  classical
  exact O.filter fun outer => needed ≤ (innerHits I event outer).card

def hitValue (event : Outer → Inner → Prop) (outer : Outer) (inner : Inner) : ℚ := by
  classical
  exact if event outer inner then 1 else 0

def nestedMass (O : Finset Outer) (I : Finset Inner)
    (event : Outer → Inner → Prop) : ℚ :=
  avg O fun outer => avg I fun inner => hitValue event outer inner

def ceiling (O : Finset Outer) (I : Finset Inner) : ℚ :=
  (28 : ℚ) / (O.card : ℚ) + 3 / (I.card : ℚ)

attribute [irreducible] innerHits forkable

theorem mem_forkable (O : Finset Outer) (I : Finset Inner)
    (event : Outer → Inner → Prop) (needed : Nat) (outer : Outer) :
    outer ∈ forkable O I event needed ↔
      outer ∈ O ∧ needed ≤ (innerHits I event outer).card := by
  classical
  rw [forkable]
  exact Finset.mem_filter

theorem forkable_subset (O : Finset Outer) (I : Finset Inner)
    (event : Outer → Inner → Prop) (needed : Nat) :
    forkable O I event needed ⊆ O := by
  intro outer member
  exact ((mem_forkable O I event needed outer).mp member).1

theorem inner_mass_eq (I : Finset Inner) (event : Outer → Inner → Prop)
    (outer : Outer) :
    avg I (fun inner => hitValue event outer inner) =
      ((innerHits I event outer).card : ℚ) / I.card := by
  classical
  simpa only [hitValue, innerHits] using avg_indicator I (event outer)

/-- Four-inner / twenty-nine-outer raw bound, before instantiating `event`
with an actual verifier history.  The additive form is deliberately used:
it is valid without an independence assertion beyond the displayed nested
finite experiment. -/
theorem nested_mass_le (O : Finset Outer) (I : Finset Inner)
    (outerNonempty : O.Nonempty) (innerNonempty : I.Nonempty)
    (event : Outer → Inner → Prop)
    (fewOuter : (forkable O I event 4).card ≤ 28) :
    nestedMass O I event ≤ ceiling O I := by
  classical
  have innerCardPositive : (0 : ℚ) < I.card := by
    exact_mod_cast innerNonempty.card_pos
  have unit (outer : Outer) (member : outer ∈ O) :
      avg I (fun inner => hitValue event outer inner) ≤ 1 := by
    apply avg_le I innerNonempty
    intro inner _
    classical
    simp only [hitValue]
    split <;> norm_num
  have outside (outer : Outer) (member : outer ∈ O)
      (notForkable : outer ∉ forkable O I event 4) :
      avg I (fun inner => hitValue event outer inner) ≤ 3 / (I.card : ℚ) := by
    classical
    rw [inner_mass_eq]
    have notFour : ¬4 ≤ (innerHits I event outer).card := by
      intro four
      exact notForkable ((mem_forkable O I event 4 outer).mpr ⟨member, four⟩)
    have atMostThree : ((innerHits I event outer).card : ℚ) ≤ 3 := by
      exact_mod_cast (show (innerHits I event outer).card ≤ 3 by omega)
    exact (div_le_div_iff_of_pos_right innerCardPositive).mpr atMostThree
  have bounded :
      avg O (fun outer => avg I (fun inner => hitValue event outer inner)) ≤
        ((forkable O I event 4).card : ℚ) / (O.card : ℚ) +
          (3 : ℚ) / (I.card : ℚ) :=
    avg_exception O (forkable O I event 4) outerNonempty
      (forkable_subset O I event 4) (fun outer =>
        avg I (fun inner => hitValue event outer inner))
      ((3 : ℚ) / (I.card : ℚ)) (by positivity) unit outside
  rw [nestedMass, ceiling]
  have castFew : ((forkable O I event 4).card : ℚ) ≤ 28 := by
    exact_mod_cast fewOuter
  have denominator : (0 : ℚ) ≤ (O.card : ℚ) := Nat.cast_nonneg O.card
  have fractionBound :
      ((forkable O I event 4).card : ℚ) / (O.card : ℚ) ≤
        (28 : ℚ) / (O.card : ℚ) :=
    div_le_div_of_nonneg_right castFew denominator
  linarith only [bounded, fractionBound]

/-- The deterministic extraction bridge is exposed as the implication
`29 <= forkable.card -> X`.  Thus an extractor failure, rather than absence
of a radius classifier, is what licenses the probability bound. -/
theorem nested_mass_le_of_not_extracted (O : Finset Outer) (I : Finset Inner)
    (outerNonempty : O.Nonempty) (innerNonempty : I.Nonempty)
    (event : Outer → Inner → Prop)
    (X : Prop) (extract : 29 ≤ (forkable O I event 4).card → X)
    (notExtracted : ¬X) :
    nestedMass O I event ≤ ceiling O I := by
  classical
  apply nested_mass_le O I outerNonempty innerNonempty event
  have notTwentyNine : ¬29 ≤ (forkable O I event 4).card := by
    intro enough
    exact notExtracted (extract enough)
  omega

#print axioms inner_mass_eq
#print axioms mem_forkable
#print axioms forkable_subset
#print axioms nested_mass_le
#print axioms nested_mass_le_of_not_extracted
end
end AspisV8.NestedForkExtraction
