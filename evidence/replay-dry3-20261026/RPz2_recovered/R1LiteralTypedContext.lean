import R1LiteralTypedWords
import R1D18Transport
import R0P.SemSource
import R0P.SemView
import R0P.CoreExt

/-! Construct the existing semantic typed context directly from literal
decoded C1/C2 words. This is a representation bridge only. -/
set_option autoImplicit false

namespace AspisR1.LiteralTypedContext

open AspisPool.AlgorithmicCircleDecoderV7
open R0P.SemSource
open R0C.SemStatement
open AspisR1.LiteralTypedWords
open AspisR1.ExactLeafFieldCodec

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod AspisCircleGroupOrder.P) E]

def context (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (pub : R0P.Public E) (hpub : R0P.PublicBase eM.fieldRange pub)
    (c1 : C1Word) (extraClaims : Fin 29 → E) : TypedContext E (laneSubfield eM eK) where
  pub := pub
  transport := AspisR1.rowEquiv
  extraClaims := extraClaims
  W := word eM eK c1 (fun _ _ => 0)
  base := word_typed eM eK c1 (fun _ _ => 0)
  F := eM.fieldRange
  lanesF := by
    intro l hl
    simp [laneSubfield, TypedRecoveredWords.laneSubfield, hl]
  pubBase := hpub

def fullWords (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (c1 : C1Word) (c2 : C2Word) : Fin 29 → InitialWord E :=
  word eM eK c1 c2

def lane26 (W : Fin 29 → InitialWord E) : InitialWord E := W 26
def lane27 (W : Fin 29 → InitialWord E) : InitialWord E := W 27

theorem full_eq_c1_only_outside_c2 (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (c1 : C1Word) (c2 : C2Word) (l : Fin 29) (h26 : l ≠ 26) (h27 : l ≠ 27) :
    fullWords eM eK c1 c2 l =
      fullWords eM eK c1 (fun _ _ => 0) l := by
  exact LiteralTypedWords.word_eq_zeroC2Word_outside_c2 eM eK c1 c2 l h26 h27

theorem c2Words_full (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (pub : R0P.Public E) (hpub : R0P.PublicBase eM.fieldRange pub)
    (c1 : C1Word) (c2 : C2Word) (extraClaims : Fin 29 → E) :
    c2Words (context eM eK pub hpub c1 extraClaims)
      (lane26 (fullWords eM eK c1 c2))
      (lane27 (fullWords eM eK c1 c2)) =
      fullWords eM eK c1 c2 := by
  funext l
  by_cases h26 : l = 26
  · subst l
    simp [c2Words, lane26]
  · by_cases h27 : l = 27
    · subst l
      simp [c2Words, lane27]
    · simp [context, c2Words, lane26, lane27, h26, h27]
      exact (full_eq_c1_only_outside_c2 eM eK c1 c2 l h26 h27).symm

theorem c2Base_full (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (c1 : C1Word) (c2 : C2Word) :
    c2Base (laneSubfield eM eK)
      (lane26 (fullWords eM eK c1 c2))
      (lane27 (fullWords eM eK c1 c2)) := by
  have htyped := word_typed eM eK c1 c2
  constructor
  · intro i
    exact htyped 26 i
  · intro i
    exact htyped 27 i

#print axioms c2Words_full
#print axioms c2Base_full

end AspisR1.LiteralTypedContext
