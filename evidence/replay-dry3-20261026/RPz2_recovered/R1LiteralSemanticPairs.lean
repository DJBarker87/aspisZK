import R1LiteralSemanticPrefix
import R1LiteralSemanticIndex
import R1SemanticPayloadView
import R1SemanticRecordCodec
import R1LiteralSemanticCodecBridge
import R1LiteralSemanticPayloadBridge

/-! Successful literal semantic-prefix reads are represented by the canonical
typed payload-pair list, with the C2 callback fixed by the literal word at
row 2. This is a model-level list identity only. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralSemanticPairs

open AspisR1.LiteralSemanticPrefix
open AspisR1.SemanticPayloadView
open AspisR1.SemanticRecordCodec
open AspisR1.LiteralTranscript
open AspisR1.TranscriptView
open R0P.Mask

abbrev E := LiteralSemanticPrefix.E

theorem read_eq_pairs
    (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* E)
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (out : List (SemMsgZ E × E))
    (word : LiteralTranscript.C2Word)
    (hread : LiteralSemanticPrefix.read eK 0 rs = some out)
    (hlen : rs.length = 25)
    (hc2 : LiteralTranscript.c2At rs = some word) :
    ∃ payloads : (i : Fin 25) → SemanticRecordCodec.RowPayload i,
    ∃ challenges : Fin 25 → E,
      out = SemanticPayloadView.pairs
        (fun _ => LiteralSemanticPrefix.c2Pair eK word) payloads challenges := by
  have houtlen : out.length = 25 := by
    rw [LiteralSemanticPrefix.read_length eK 0 rs out hread, hlen]
  have hrowValid (i : Fin 25) :
      LiteralTranscript.valid i.val (rs[i.val]'(by rw [hlen]; exact i.isLt)).1 := by
    have hi : i.val < rs.length := by rw [hlen]; exact i.isLt
    obtain ⟨_, parsed, _, hparsed, _, _⟩ :=
      LiteralSemanticIndex.read_index eK 0 rs out hread i.val hi
    have hparsed' : LiteralSemanticPrefix.parseMessage eK i (rs[i.val]'hi).1 =
        some parsed := by
      simpa using hparsed
    by_contra hbad
    simp [LiteralSemanticPrefix.parseMessage, hbad] at hparsed'
  have hcarrying (i : Fin 25) :
      LiteralSemanticPayloadBridge.CarriesC2 word
        (rs[i.val]'(by rw [hlen]; exact i.isLt)).1 := by
    intro bs actual hm
    have hvalid : LiteralTranscript.valid i.val (.c2 bs actual) := by
      rw [← hm]
      exact hrowValid i
    have hrow2 := LiteralSemanticPayloadBridge.valid_c2_row i.val bs actual hvalid
    have htwo : 2 < rs.length := by rw [hlen]; omega
    have hm2 : (rs[2]'htwo).1 = .c2 bs actual := by
      simpa only [hrow2] using hm
    have hh := hc2
    unfold LiteralTranscript.c2At at hh
    rw [List.getElem?_eq_getElem htwo] at hh
    simp only [Option.bind_some, hm2] at hh
    exact Option.some.inj hh
  have hrow (i : Fin 25) :
      ∃ payload : SemanticRecordCodec.RowPayload i, ∃ c : E,
        out[i.val]'(by simpa [houtlen] using i.isLt) =
          (SemanticPayloadView.toMessage (fun _ => LiteralSemanticPrefix.c2Pair eK word)
            payload.val, c) := by
    have hi : i.val < rs.length := by rw [hlen]; exact i.isLt
    obtain ⟨_, parsed, c, hparsed, _, hindex⟩ :=
      LiteralSemanticIndex.read_index eK 0 rs out hread i.val hi
    have hparsed' : LiteralSemanticPrefix.parseMessage eK i (rs[i.val]'hi).1 =
        some parsed := by
      simpa using hparsed
    have hv : LiteralTranscript.valid i.val (rs[i.val]'hi).1 := hrowValid i
    obtain ⟨payload, hdecode⟩ :=
      LiteralSemanticCodecBridge.decode_of_parseMessage eK i
        (rs[i.val]'hi).1 parsed hparsed'
    have hmap :
        (SemanticRecordCodec.decode i
          (LiteralSemanticCodecBridge.record (rs[i.val]'hi).1)).map
          (fun p => SemanticPayloadView.toMessage
            (LiteralSemanticCodecBridge.callback eK (rs[i.val]'hi).1) p.val) =
          some parsed := by
      have h := hparsed'
      rw [LiteralSemanticCodecBridge.parseMessage_eq_decode] at h
      simpa only [if_pos hv] using h
    rw [hdecode] at hmap
    simp only [Option.map_some] at hmap
    have hcallback :
        SemanticPayloadView.toMessage
          (LiteralSemanticCodecBridge.callback eK (rs[i.val]'hi).1) payload.val =
        SemanticPayloadView.toMessage
          (fun _ => LiteralSemanticPrefix.c2Pair eK word) payload.val :=
      LiteralSemanticPayloadBridge.callback_toMessage eK i payload
        (rs[i.val]'hi).1 word hv (hcarrying i)
    have hp : parsed = SemanticPayloadView.toMessage
        (fun _ => LiteralSemanticPrefix.c2Pair eK word) payload.val :=
      (Option.some.inj hmap).symm.trans hcallback
    refine ⟨payload, c, ?_⟩
    simpa [hp] using hindex
  let payloads : (i : Fin 25) → SemanticRecordCodec.RowPayload i :=
    fun i => Classical.choose (hrow i)
  let challenges : Fin 25 → E :=
    fun i => Classical.choose (Classical.choose_spec (hrow i))
  have hchosen (i : Fin 25) :
      out[i.val]'(by simpa [houtlen] using i.isLt) =
        (SemanticPayloadView.toMessage
            (fun _ => LiteralSemanticPrefix.c2Pair eK word) (payloads i).val,
          challenges i) :=
    Classical.choose_spec (Classical.choose_spec (hrow i))
  refine ⟨payloads, challenges, ?_⟩
  apply List.ext_getElem
  · simp only [SemanticPayloadView.pairs, List.length_ofFn, houtlen]
  · intro n h₁ h₂
    let i : Fin 25 := ⟨n, by simpa [houtlen] using h₁⟩
    have heq := hchosen i
    simpa only [SemanticPayloadView.pairs, List.getElem_ofFn, i] using heq

#print axioms read_eq_pairs

end AspisR1.LiteralSemanticPairs
end
