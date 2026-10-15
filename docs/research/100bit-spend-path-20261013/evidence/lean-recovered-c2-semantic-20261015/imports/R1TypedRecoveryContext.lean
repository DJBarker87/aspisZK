import R1TypedRecoveredWords
import R1D18Transport
import R0P.SemSource
import R0P.SemView
import R0P.CoreExt

/-! Build the existing semantic typed context from the total strict-decoder
word representation. This is a representation bridge only. -/
set_option autoImplicit false

namespace AspisR1.TypedRecoveryContext

open AspisPool.AlgorithmicCircleDecoderV7
open R0P.SemSource
open R0C.SemStatement
open AspisR1.TypedRecoveredWords
open AspisR1.ExactLeafFieldCodec

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod AspisCircleGroupOrder.P) E]

def context (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (pub : R0P.Public E) (hpub : R0P.PublicBase eM.fieldRange pub)
    (c1Packed : Fin 262144 → Option (List Byte))
    (extraClaims : Fin 29 → E) : TypedContext E (laneSubfield eM eK) where
  pub := pub
  transport := AspisR1.rowEquiv
  extraClaims := extraClaims
  W := word eM eK c1Packed (fun _ => none)
  base := word_typed eM eK c1Packed (fun _ => none)
  F := eM.fieldRange
  lanesF := by
    intro l hl
    simp [laneSubfield, hl]
  pubBase := hpub

def fullWords (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (c1Packed c2Packed : Fin 262144 → Option (List Byte)) :
    Fin 29 → InitialWord E :=
  word eM eK c1Packed c2Packed

def lane26 (W : Fin 29 → InitialWord E) : InitialWord E := W 26
def lane27 (W : Fin 29 → InitialWord E) : InitialWord E := W 27

theorem full_eq_c1_only_outside_c2 (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (c1Packed c2Packed : Fin 262144 → Option (List Byte))
    (l : Fin 29) (h26 : l ≠ 26) (h27 : l ≠ 27) :
    fullWords eM eK c1Packed c2Packed l =
      fullWords eM eK c1Packed (fun _ => none) l := by
  funext i
  unfold fullWords TypedRecoveredWords.word
  by_cases hb : l.val < 26
  · simp [hb]
  · have h28 : l.val = 28 := by have := l.isLt; omega
    simp [hb, h28, h26, h27]

theorem c2Words_full (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (pub : R0P.Public E) (hpub : R0P.PublicBase eM.fieldRange pub)
    (c1Packed c2Packed : Fin 262144 → Option (List Byte))
    (extraClaims : Fin 29 → E) :
    c2Words (context eM eK pub hpub c1Packed extraClaims)
      (lane26 (fullWords eM eK c1Packed c2Packed))
      (lane27 (fullWords eM eK c1Packed c2Packed)) =
      fullWords eM eK c1Packed c2Packed := by
  funext l
  by_cases h26 : l = 26
  · subst l
    simp [c2Words, lane26]
  · by_cases h27 : l = 27
    · subst l
      simp [c2Words, lane27]
    · simp [context, c2Words, lane26, lane27, h26, h27]
      exact (full_eq_c1_only_outside_c2 eM eK c1Packed c2Packed l h26 h27).symm

theorem c2Base_full (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (c1Packed c2Packed : Fin 262144 → Option (List Byte)) :
    c2Base (laneSubfield eM eK)
      (lane26 (fullWords eM eK c1Packed c2Packed))
      (lane27 (fullWords eM eK c1Packed c2Packed)) := by
  have htyped := word_typed eM eK c1Packed c2Packed
  constructor
  · intro i
    exact htyped 26 i
  · intro i
    exact htyped 27 i

#print axioms c2Words_full
#print axioms c2Base_full

end AspisR1.TypedRecoveryContext
