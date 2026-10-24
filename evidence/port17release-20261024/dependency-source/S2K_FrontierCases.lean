import S2K_Serialization

/-! Concrete-level composition. Native Kani certificates are external checks;
this theorem does not turn them into Lean axioms. Its twenty named ports must
be instantiated by a source-to-model interpretation before native closure.
Each port requires the same input buffer/node and both write and frame facts. -/
set_option autoImplicit false
namespace AspisR1.S2K.FrontierCases
open Aeneas.Std
abbrev Buffer := Fin 688 → U8
abbrev Node := Fin 32 → U8

def Contract (step : Nat → Buffer → Node → Buffer) (level : Nat) : Prop :=
  ∀ before node i,
    step level before node i =
      if h : 48 + 32 * level ≤ i.val ∧ i.val < 80 + 32 * level then
        node ⟨i.val - (48 + 32 * level), by omega⟩
      else before i

/-- Exhaustive source-level dispatch; no reduction of a 688-byte array. -/
theorem concrete_cases (step : Nat → Buffer → Node → Buffer)
    (level00 : Contract step 0)
    (level01 : Contract step 1)
    (level02 : Contract step 2)
    (level03 : Contract step 3)
    (level04 : Contract step 4)
    (level05 : Contract step 5)
    (level06 : Contract step 6)
    (level07 : Contract step 7)
    (level08 : Contract step 8)
    (level09 : Contract step 9)
    (level10 : Contract step 10)
    (level11 : Contract step 11)
    (level12 : Contract step 12)
    (level13 : Contract step 13)
    (level14 : Contract step 14)
    (level15 : Contract step 15)
    (level16 : Contract step 16)
    (level17 : Contract step 17)
    (level18 : Contract step 18)
    (level19 : Contract step 19)
    (level : Nat) (range : level < 20) : Contract step level := by
  have cases : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 ∨ level = 4 ∨ level = 5 ∨ level = 6 ∨ level = 7 ∨ level = 8 ∨ level = 9 ∨ level = 10 ∨ level = 11 ∨ level = 12 ∨ level = 13 ∨ level = 14 ∨ level = 15 ∨ level = 16 ∨ level = 17 ∨ level = 18 ∨ level = 19 := by omega
  rcases cases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19
  · subst level; exact level00
  · subst level; exact level01
  · subst level; exact level02
  · subst level; exact level03
  · subst level; exact level04
  · subst level; exact level05
  · subst level; exact level06
  · subst level; exact level07
  · subst level; exact level08
  · subst level; exact level09
  · subst level; exact level10
  · subst level; exact level11
  · subst level; exact level12
  · subst level; exact level13
  · subst level; exact level14
  · subst level; exact level15
  · subst level; exact level16
  · subst level; exact level17
  · subst level; exact level18
  · subst level; exact level19

#print axioms concrete_cases
end AspisR1.S2K.FrontierCases
