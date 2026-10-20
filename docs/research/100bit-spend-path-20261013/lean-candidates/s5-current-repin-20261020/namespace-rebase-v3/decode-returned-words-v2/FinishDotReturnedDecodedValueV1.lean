import AspisR1FinishDotReturnedProductWordsV2
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FinishDotReturnedDecodedValueV1
open AspisR1FinishDotReturnedProductWords AspisR1FinishDotDecodedProductTrace

def finishEWords (out : AspisR1FinishDotDecodedProductTrace.FinishE) :
    (AspisV8R17.GeneratedQM31Products.WordPair × AspisV8R17.GeneratedQM31Products.WordPair) ×
    (AspisV8R17.GeneratedQM31Products.WordPair × AspisV8R17.GeneratedQM31Products.WordPair) :=
  (finishQMWords out.c0, finishQMWords out.c1)

/-- Decode the concrete returned `FinishE` through its actual current wide
carrier; this equation exposes its two QM word tuples without changing the
source result type. -/
theorem decodeFinish_eq_word_tower (out : FinishE) :
    AspisR1CurrentWide.Proof.decodeFinish out =
      ⟨AspisV8R17.QM31WordTower.decodeQ (finishQMWords out.c0),
       AspisV8R17.QM31WordTower.decodeQ (finishQMWords out.c1)⟩ := by
  change ⟨AspisR1CurrentWide.Proof.decodeQM
      (AspisR1CurrentWide.Proof.ofFinishQM out.c0),
    AspisR1CurrentWide.Proof.decodeQM
      (AspisR1CurrentWide.Proof.ofFinishQM out.c1)⟩ = _
  rw [AspisR1FinishDotReturnedProductWords.current_finish_qm_decode_word_tower,
      AspisR1FinishDotReturnedProductWords.current_finish_qm_decode_word_tower]

#print axioms decodeFinish_eq_word_tower
end AspisR1FinishDotReturnedDecodedValueV1
