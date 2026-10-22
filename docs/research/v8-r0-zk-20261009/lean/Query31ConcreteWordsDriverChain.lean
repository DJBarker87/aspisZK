import Query31ModelDriverChain
import QueryScanConcreteWordsDecoder
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace Query31ConcreteWordsDriverChain
open Query31ModelDriverChain
open Query31ModelScanCall Query31ExplicitListLoop Query31ExplicitScanBody AspisV8R19.Q22WordScan

/-- The exact byte block parser and 18-bit masking operation in r0_transcript.rs. -/
def actualQueryWords : Array Std.U8 32#usize → Result (Array Std.U32 8#usize) :=
  AspisR1QueryScanUnrolled.r0_transcript.query_words

/-- Every selected successful block decode in a Q22 scan chain is the ordered
    little-endian word list with the source query mask applied. -/
theorem chain_words_are_concrete
    (blocks : Array (Array Std.U8 32#usize) 8#usize)
    (s0 sf : Query31ModelDriverChain.QueryScan)
    (evidence : List (BlockEvidence actualQueryWords blocks))
    (hchain : Q22ScanChain actualQueryWords blocks s0 evidence sf) :
    ∀ e ∈ evidence, e.words.val = (List.range 8).map
      (fun j => AspisR1QueryScanUnrolled.r0_transcript.queryMaskWord
        (AspisR1QueryScanUnrolled.r0_transcript.blockRankWord e.bytes j)) := by
  revert hchain
  induction evidence generalizing s0 sf with
  | nil =>
      intro hchain e he
      simp at he
  | cons head tail ih =>
      intro hchain e he
      cases hchain with
      | @cons s s' sf head tail hs hcall hsemantic hvalid htail =>
          simp only [List.mem_cons] at he
          rcases he with hhead | htailmem
          · subst e
            exact AspisR1QueryScanUnrolled.r0_transcript.query_words_success_byte_mask
              head.bytes head.words head.decode_ok
          · exact ih s' sf htail e htailmem

/-- The successful concrete decoder driver yields a Q22 chain whose per-block
    decoded words are exactly those read from the selected 32-byte blocks. -/
theorem successful_driver_has_concrete_q22_chain
    (blocks advances : Array (Array Std.U8 32#usize) 8#usize)
    (s0 : Query31ModelDriverChain.QueryScan) (accepted : Array Std.U32 22#usize)
    (next : Array Std.U8 32#usize)
    (hstart : validState s0)
    (hsuccess : AspisR1Query31Transcript.queries_from_pairs_with_scan
      (modelScanFn actualQueryWords) s0 blocks advances =
        .ok (core.result.Result.Ok (accepted, next))) :
    ∃ evidence sf,
      Q22ScanChain actualQueryWords blocks s0 evidence sf ∧
      evidence.length ≤ 8 ∧ validState sf ∧
      ∀ e ∈ evidence, e.words.val = (List.range 8).map
        (fun j => AspisR1QueryScanUnrolled.r0_transcript.queryMaskWord
          (AspisR1QueryScanUnrolled.r0_transcript.blockRankWord e.bytes j)) := by
  obtain ⟨evidence, sf, hchain, hlen, hvalid⟩ :=
    successful_driver_q22_chain actualQueryWords blocks advances s0 accepted next hstart hsuccess
  exact ⟨evidence, sf, hchain, hlen, hvalid,
    chain_words_are_concrete blocks s0 sf evidence hchain⟩

#print axioms chain_words_are_concrete
#print axioms successful_driver_has_concrete_q22_chain
end Query31ConcreteWordsDriverChain
