import R1LiteralTranscript
import R1LiteralSemanticPrefix
import R1LiteralChallengeRead
import R1LiteralTypedWords
import R1SelectedOpeningFunctionals
import R1SelectedChallengeMap
import R1ExactBaseProjection

/-! Assemble the literal prefix fields used by the selected opening model.
The result is a strict typed view of existing message/challenge entries. It
does not assert source refinement, acceptance, or a shared-oracle density law. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralOpeningView

open AspisR1.LiteralTranscript
open AspisR1.LiteralSemanticPrefix
open AspisR1.LiteralChallengeRead
open AspisR1.SelectedOpeningFunctionals
open AspisV8R15.ExactTowerBase
open AspisWideTower

abbrev E := WideExact
abbrev eK : QM31Exact →+* E := algebraMap QM31Exact E
abbrev W := Fin 29 → AspisPool.AlgorithmicCircleDecoderV7.InitialWord E
abbrev Functional := AspisR1.ConcreteBinding.Functional E

structure View where
  c1 : LiteralTranscript.C1Word
  c2 : LiteralTranscript.C2Word
  word : W
  semantic : List (R0P.Mask.SemMsgZ E × E)
  semantic_length : semantic.length = 25
  challenge25 : E
  challenge26 : E
  circlePoints : Fin 2 → AspisR0.ChordGeometry.Point AspisWideTower.WideExact
  functionals : Fin 6 → Functional
  baseFunctional : Functional

/-- Read the typed opening context from literal message and challenge entries.
The semantic prefix must contain exactly 25 rows; the two ordinary challenges
at rows 25 and 26 are projected through the selected total circle maps. -/
def read (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge)) :
    Option View := do
  if hprefix : (rs.take 25).length = 25 then
    let c1 ← LiteralTranscript.c1At rs
    let c2 ← LiteralTranscript.c2At rs
    match hsem : LiteralSemanticPrefix.read eK 0 (rs.take 25) with
    | none => none
    | some semantic => do
        let z0 ← LiteralChallengeRead.ordinaryAt rs 25
        let z1 ← LiteralChallengeRead.ordinaryAt rs 26
        let word := LiteralTypedWords.word ExactBaseProjection.embed eK c1 c2
        let semanticChallenges := semantic.map Prod.snd
        let circlePoints : Fin 2 → AspisR0.ChordGeometry.Point AspisWideTower.WideExact := fun i =>
          if i.val = 0 then
            R0P.SemSource.circleSampleParameter0 (SelectedChallengeMap.rhoOf z0)
          else
            R0P.SemSource.circleSampleParameter1 (SelectedChallengeMap.rhoOf z1)
        pure ⟨c1, c2, word, semantic,
          by
            have hlen := LiteralSemanticPrefix.read_length eK 0
              (rs.take 25) semantic hsem
            rw [hlen]
            exact hprefix,
          z0, z1, circlePoints,
          SelectedOpeningFunctionals.functionals (E := AspisWideTower.WideExact)
            semanticChallenges circlePoints,
          SelectedOpeningFunctionals.rawBase (E := AspisWideTower.WideExact)
            semanticChallenges circlePoints⟩
  else none

theorem read_semantic_length
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (v : View) (h : read rs = some v) : v.semantic.length = 25 := by
  exact v.semantic_length

#print axioms read
#print axioms read_semantic_length

end AspisR1.LiteralOpeningView
end
