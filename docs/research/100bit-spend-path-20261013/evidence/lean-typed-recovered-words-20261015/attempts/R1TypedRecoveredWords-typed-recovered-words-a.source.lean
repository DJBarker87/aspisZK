import R1CandidateDescent
import R1MixedLeafDecoder

/-! Total, zero-default projection from strict C1/C2 leaf decoders to the
protocol's 29 typed lanes.  This is a representation map only; it does not
connect recovered Merkle bytes to a protocol transcript. -/
set_option autoImplicit false

namespace AspisR1.TypedRecoveredWords

open AspisR1.MixedLeafDecoder
open AspisR1.MixedLeafEncoding
open AspisR1.ExactLeafFieldCodec
open AspisPool.AlgorithmicCircleDecoderV7

abbrev C1 := AspisR1.MixedLeafEncoding.C1
abbrev C2 := AspisR1.MixedLeafEncoding.C2
abbrev C1Slot := AspisR1.MixedLeafEncoding.C1Slot
abbrev C2Slot := AspisR1.MixedLeafEncoding.C2Slot

def zeroC1 : C1 := fun _ => (fun _ => 0, 0)

def zeroC2 : C2 := fun _ _ => 0

def queryLeaf (i : Fin 1048576) : Fin 262144 :=
  ⟨i.val / 4, by have := i.isLt; omega⟩

def querySlot (i : Fin 1048576) : Fin 4 :=
  ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩

def decodeC1At (packed : Fin 262144 → Option (List Byte))
    (leaf : Fin 262144) : Option C1 :=
  (packed leaf).bind decodeC1

def decodeC2At (packed : Fin 262144 → Option (List Byte))
    (leaf : Fin 262144) : Option C2 :=
  (packed leaf).bind decodeC2

def c1Value (packed : Fin 262144 → Option (List Byte)) (i : Fin 1048576) : C1Slot :=
  ((decodeC1At packed (queryLeaf i)).getD zeroC1) (querySlot i)

def c2Value (packed : Fin 262144 → Option (List Byte)) (i : Fin 1048576) : C2Slot :=
  ((decodeC2At packed (queryLeaf i)).getD zeroC2) (querySlot i)

def laneSubfield {E : Type} [Field E]
    (eM : M31Exact →+* E) (eK : QM31Exact →+* E) (l : Fin 29) : Subfield E :=
  if l.val < 26 then eM.fieldRange else eK.fieldRange

def word {E : Type} [Field E]
    (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (c1Packed c2Packed : Fin 262144 → Option (List Byte)) : InitialWord E :=
  fun l i =>
    if hbase : l.val < 26 then
      eM ((c1Value c1Packed i).1 ⟨l.val, hbase⟩)
    else
      eK (if h26 : l.val = 26 then
        (c2Value c2Packed i) ⟨0, by decide⟩
      else if h27 : l.val = 27 then
        (c2Value c2Packed i) ⟨1, by decide⟩
      else
        (c1Value c1Packed i).2)

theorem word_typed {E : Type} [Field E]
    (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (c1Packed c2Packed : Fin 262144 → Option (List Byte)) :
    AspisR1.CandidateDescent.WordTyped (laneSubfield eM eK) (word eM eK c1Packed c2Packed) := by
  intro l i
  unfold word laneSubfield
  by_cases hbase : l.val < 26
  · simp only [hbase, ↓reduceDIte]
    exact eM.mem_fieldRange_self _
  · simp only [hbase, ↓reduceDIte]
    exact eK.mem_fieldRange_self _

theorem word_c1_base_of_decode {E : Type} [Field E]
    (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (c1Packed c2Packed : Fin 262144 → Option (List Byte))
    (i : Fin 1048576) (l : Fin 26) (c : C1)
    (hdecode : decodeC1At c1Packed (queryLeaf i) = some c) :
    word eM eK c1Packed c2Packed ⟨l.val, by have := l.isLt; omega⟩ i =
      eM ((c (querySlot i)).1 l) := by
  simp [word, hdecode, queryLeaf, querySlot, l.isLt]

theorem word_c1_tail_of_decode {E : Type} [Field E]
    (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (c1Packed c2Packed : Fin 262144 → Option (List Byte))
    (i : Fin 1048576) (c : C1)
    (hdecode : decodeC1At c1Packed (queryLeaf i) = some c) :
    word eM eK c1Packed c2Packed ⟨28, by decide⟩ i =
      eK ((c (querySlot i)).2) := by
  simp [word, hdecode, queryLeaf, querySlot]

theorem word_c2_first_of_decode {E : Type} [Field E]
    (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (c1Packed c2Packed : Fin 262144 → Option (List Byte))
    (i : Fin 1048576) (c : C2)
    (hdecode : decodeC2At c2Packed (queryLeaf i) = some c) :
    word eM eK c1Packed c2Packed ⟨26, by decide⟩ i =
      eK ((c (querySlot i)) ⟨0, by decide⟩) := by
  simp [word, hdecode, queryLeaf, querySlot]

theorem word_c2_second_of_decode {E : Type} [Field E]
    (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (c1Packed c2Packed : Fin 262144 → Option (List Byte))
    (i : Fin 1048576) (c : C2)
    (hdecode : decodeC2At c2Packed (queryLeaf i) = some c) :
    word eM eK c1Packed c2Packed ⟨27, by decide⟩ i =
      eK ((c (querySlot i)) ⟨1, by decide⟩) := by
  simp [word, hdecode, queryLeaf, querySlot]

#print axioms word_typed
#print axioms word_c1_base_of_decode
#print axioms word_c1_tail_of_decode
#print axioms word_c2_first_of_decode
#print axioms word_c2_second_of_decode

end AspisR1.TypedRecoveredWords
