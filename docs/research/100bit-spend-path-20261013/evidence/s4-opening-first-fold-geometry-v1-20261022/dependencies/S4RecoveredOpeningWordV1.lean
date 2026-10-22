import S4CanonicalOpeningV1
import R1LiteralTypedWords
set_option autoImplicit false
namespace AspisR1.S4RecoveredOpeningWordV1
open AspisR1.MixedLeafDecoder AspisR1.MixedLeafEncoding AspisR1.ExactLeafFieldCodec
open AspisR1.TypedRecoveredWords
open AspisV8R19.DuplexFrames

theorem decoded_pair_matches_recovered_word {E : Type} [Field E]
    (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (packed1 packed2 : Fin 262144 → Option Bytes) (i : Fin 1048576)
    (bs : Bytes) (c1 : MixedLeafEncoding.C1) (c2 : MixedLeafEncoding.C2)
    (hp1 : packed1 (queryLeaf i) = some (bs.take 480))
    (hp2 : packed2 (queryLeaf i) = some (bs.drop 480))
    (hd1 : decodeC1 (bs.take 480) = some c1)
    (hd2 : decodeC2 (bs.drop 480) = some c2) :
    ∀ lane, TypedRecoveredWords.word eM eK packed1 packed2 lane i =
      LiteralTypedWords.word eM eK (fun _ => c1 (querySlot i))
        (fun _ => c2 (querySlot i)) lane i := by
  have hc1 : decodeC1At packed1 (queryLeaf i) = some c1 := by
    simp only [decodeC1At, hp1, Option.bind_some, hd1]
  have hc2 : decodeC2At packed2 (queryLeaf i) = some c2 := by
    simp only [decodeC2At, hp2, Option.bind_some, hd2]
  intro lane
  simp only [TypedRecoveredWords.word, LiteralTypedWords.word, c1Value, c2Value,
    hc1, hc2, Option.getD_some]

/-- Primitive recovered-byte map facts suffice to bind every decoded local
lane to the existing global word; no desired word equality is assumed. -/
theorem canonical_opening_matches_recovered_word {E : Type} [Field E]
    (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (packed1 packed2 : Fin 262144 → Option Bytes) (i : Fin 1048576)
    (bs : Bytes) (hlen : bs.length = 608) (hc : OraclePortCompactDraft.canonical bs)
    (hp1 : packed1 (queryLeaf i) = some (bs.take 480))
    (hp2 : packed2 (queryLeaf i) = some (bs.drop 480)) :
    ∃ c1 c2, decodeC1 (bs.take 480) = some c1 ∧ decodeC2 (bs.drop 480) = some c2 ∧
      bs = encodeC1 c1 ++ encodeC2 c2 ∧
      ∀ lane, TypedRecoveredWords.word eM eK packed1 packed2 lane i =
        LiteralTypedWords.word eM eK (fun _ => c1 (querySlot i))
          (fun _ => c2 (querySlot i)) lane i := by
  obtain ⟨c1,c2,hd1,hd2,hbytes⟩ :=
    S4CanonicalOpeningV1.canonical_opening_decode_exists bs hlen hc
  exact ⟨c1,c2,hd1,hd2,hbytes,
    decoded_pair_matches_recovered_word eM eK packed1 packed2 i bs c1 c2 hp1 hp2 hd1 hd2⟩
#print axioms decoded_pair_matches_recovered_word
#print axioms canonical_opening_matches_recovered_word
end AspisR1.S4RecoveredOpeningWordV1
