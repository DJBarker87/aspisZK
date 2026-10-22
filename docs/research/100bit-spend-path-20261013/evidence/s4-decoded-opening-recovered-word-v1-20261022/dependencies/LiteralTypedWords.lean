import R1TypedRecoveredWords

/-! A direct typed representation of a pair of decoded literal C1/C2 words.
This exposes the same 29-lane layout as `TypedRecoveredWords.word` without
using the total zero-default projections. It is only a representation bridge.
-/
set_option autoImplicit false

namespace AspisR1.LiteralTypedWords

open AspisPool.AlgorithmicCircleDecoderV7
open AspisR1.MixedLeafEncoding
open AspisR1.TypedRecoveredWords
open AspisR1.ExactLeafFieldCodec

abbrev C1Word := Fin 1048576 → MixedLeafEncoding.C1Slot
abbrev C2Word := Fin 1048576 → MixedLeafEncoding.C2Slot

def laneSubfield {E : Type} [Field E]
    (eM : M31Exact →+* E) (eK : QM31Exact →+* E) (l : Fin 29) : Subfield E :=
  TypedRecoveredWords.laneSubfield eM eK l

/-- The literal word uses the C1 and C2 values directly at each index. -/
def word {E : Type} [Field E]
    (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (c1 : C1Word) (c2 : C2Word) : Fin 29 → InitialWord E :=
  fun l i =>
    if hbase : l.val < 26 then
      eM ((c1 i).1 ⟨l.val, hbase⟩)
    else
      eK (if h26 : l.val = 26 then
        (c2 i) ⟨0, by decide⟩
      else if h27 : l.val = 27 then
        (c2 i) ⟨1, by decide⟩
      else
        (c1 i).2)

def zeroC2Word {E : Type} [Field E]
    (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (c1 : C1Word) : Fin 29 → InitialWord E :=
  word eM eK c1 (fun _ _ => 0)

theorem word_typed {E : Type} [Field E]
    (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (c1 : C1Word) (c2 : C2Word) :
    AspisR1.CandidateDescent.WordTyped (laneSubfield eM eK) (word eM eK c1 c2) := by
  intro l i
  unfold word laneSubfield TypedRecoveredWords.laneSubfield
  by_cases hbase : l.val < 26
  · simp only [hbase, ↓reduceDIte]
    exact eM.mem_fieldRange_self _
  · simp only [hbase, ↓reduceDIte]
    exact eK.mem_fieldRange_self _

theorem word_recovered_eq {E : Type} [Field E]
    (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (c1Packed c2Packed : Fin 262144 → Option (List Byte)) :
    word eM eK (TypedRecoveredWords.c1Value c1Packed)
        (TypedRecoveredWords.c2Value c2Packed) =
      TypedRecoveredWords.word eM eK c1Packed c2Packed := rfl

theorem word_eq_zeroC2Word_outside_c2 {E : Type} [Field E]
    (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (c1 : C1Word) (c2 : C2Word) (l : Fin 29)
    (h26 : l ≠ 26) (h27 : l ≠ 27) :
    word eM eK c1 c2 l = zeroC2Word eM eK c1 l := by
  funext i
  dsimp only [zeroC2Word]
  unfold word
  by_cases hb : l.val < 26
  · simp [hb]
  · have h28 : l.val = 28 := by have := l.isLt; omega
    simp [hb, h28, h26, h27]

#print axioms word_typed
#print axioms word_recovered_eq
#print axioms word_eq_zeroC2Word_outside_c2

end AspisR1.LiteralTypedWords
