import Query31SourceCalls
import RPz7_Query31DigestInputBridge
import Query31ArrayReadback
import RPz7_ExtractedSourceDigestOracle
open Aeneas Aeneas.Std Result
set_option autoImplicit false
noncomputable section

namespace AspisR1PublicPreparation.Query31SourceSchedule
open AspisR1PublicPreparation
open FS FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open SourceDigestOracle SourceDigestAddresses

/-- A successful extracted squeeze call is the retained functional oracle at
its exact transcript squeeze address. The concrete digest implementation D is
kept explicit; this asserts no random-oracle property. -/
theorem squeeze_call_functional {H M Cv : Type} {L : Nat}
    {D : aspis_core.Digest32 H} {hash : H}
    (p : Params M Cv L) (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (c : DigestCall D hash) (htag : c.tag = 1#u8) :
    decodeState c.output =
      SourceDigestOracle.oracle D hash pubInput root length
        (squeezeA p (decodeState c.state)) := by
  have hin : c.input = TranscriptStep.readParts c.state 1#u8 := by
    rw [← htag]
    exact digestCall_input_eq_readParts c
  have hd : D.digest hash (TranscriptStep.readParts c.state 1#u8) = ok c.output := by
    rw [← hin]
    exact c.hdigest
  exact SourceDigestOracle.oracle_at D hash pubInput root length
    (.read c.state 1#u8) (squeezeA p (decodeState c.state)) c.output
    (SourceDigestAddresses.squeeze_address p c.state) hd

/-- The corresponding actual advance call uses the retained advance address. -/
theorem advance_call_functional {H M Cv : Type} {L : Nat}
    {D : aspis_core.Digest32 H} {hash : H}
    (p : Params M Cv L) (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (c : DigestCall D hash) (htag : c.tag = 2#u8) :
    decodeState c.output =
      SourceDigestOracle.oracle D hash pubInput root length
        (advanceA p (decodeState c.state)) := by
  have hin : c.input = TranscriptStep.readParts c.state 2#u8 := by
    rw [← htag]
    exact digestCall_input_eq_readParts c
  have hd : D.digest hash (TranscriptStep.readParts c.state 2#u8) = ok c.output := by
    rw [← hin]
    exact c.hdigest
  exact SourceDigestOracle.oracle_at D hash pubInput root length
    (.read c.state 2#u8) (advanceA p (decodeState c.state)) c.output
    (SourceDigestAddresses.advance_address p c.state) hd

/-- Both calls of one source pair have the exact mathematical address, while
retaining the actual emitted digest outputs. -/
theorem digestPair_functional {H M Cv : Type} {L : Nat}
    {D : aspis_core.Digest32 H} {hash : H}
    (p : Params M Cv L) (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (pair : DigestPair D hash) :
    decodeState pair.squeeze.output =
      SourceDigestOracle.oracle D hash pubInput root length
        (squeezeA p (decodeState pair.state)) ∧
    decodeState pair.advance.output =
      SourceDigestOracle.oracle D hash pubInput root length
        (advanceA p (decodeState pair.state)) := by
  constructor
  · rw [← pair.hsqueezeState]
    exact squeeze_call_functional p pubInput root length pair.squeeze pair.hsqueezeTag
  · rw [← pair.hadvanceState]
    exact advance_call_functional p pubInput root length pair.advance pair.hadvanceTag

/-- A successful actual queries call exposes eight ordered source digest pairs,
and every pair is interpreted at its retained mathematical squeeze/advance
addresses. Decoder and embedding behavior remain in B. -/
theorem queries_success_pairs_functional_full {H M Cv : Type} {L : Nat}
    (B : QueriesModel.Boundaries) (D : aspis_core.Digest32 H)
    (p : Params M Cv L) (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (self after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (out : Array U32 22#usize)
    (h : QueriesModel.queries B D self row payload = ok (.Ok out,after)) :
    ∃ absorbed blocks advances selected,
      ∃ pairs : List (DigestPair D absorbed.hash),
        transcript.Transcript.absorb D self row payload = ok absorbed ∧
        B.decode blocks advances = ok (.Ok (out,selected)) ∧
        after = {absorbed with state := selected} ∧
        pairs.length = 8 ∧
        (∃ first rest, pairs = first :: rest ∧ first.state = absorbed.state) ∧
        stateChain pairs ∧
        (∀ pair ∈ pairs,
          decodeState pair.squeeze.output =
            SourceDigestOracle.oracle D absorbed.hash pubInput root length
              (squeezeA p (decodeState pair.state)) ∧
          decodeState pair.advance.output =
            SourceDigestOracle.oracle D absorbed.hash pubInput root length
              (advanceA p (decodeState pair.state))) ∧
        materializedOutputs pairs blocks advances := by
  obtain ⟨absorbed, blocks, advances, selected, pairs, habs, hdecode, hafter,
      hlen, hfirst, hchain, hmaterial⟩ :=
    queries_success_with_digest_pairs_full B D self after row payload out h
  refine ⟨absorbed, blocks, advances, selected, pairs, habs, hdecode, hafter,
    hlen, hfirst, hchain, ?_, hmaterial⟩
  intro pair hp
  exact digestPair_functional p pubInput root length pair

/-- Original oracle-address projection, retaining compatibility for consumers
that only need successful calls and not the adjacent state chain. -/
theorem queries_success_pairs_functional {H M Cv : Type} {L : Nat}
    (B : QueriesModel.Boundaries) (D : aspis_core.Digest32 H)
    (p : Params M Cv L) (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (self after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (out : Array U32 22#usize)
    (h : QueriesModel.queries B D self row payload = ok (.Ok out,after)) :
    ∃ absorbed blocks advances selected,
      ∃ pairs : List (DigestPair D absorbed.hash),
        transcript.Transcript.absorb D self row payload = ok absorbed ∧
        B.decode blocks advances = ok (.Ok (out,selected)) ∧
        after = {absorbed with state := selected} ∧ pairs.length = 8 ∧
        ∀ pair ∈ pairs,
          decodeState pair.squeeze.output =
            SourceDigestOracle.oracle D absorbed.hash pubInput root length
              (squeezeA p (decodeState pair.state)) ∧
          decodeState pair.advance.output =
            SourceDigestOracle.oracle D absorbed.hash pubInput root length
              (advanceA p (decodeState pair.state)) := by
  obtain ⟨absorbed, blocks, advances, selected, pairs, habs, hdecode, hafter,
    hlen, _hfirst, _hchain, hfunctional, _hmaterial⟩ :=
      queries_success_pairs_functional_full B D p pubInput root length self after row payload out h
  exact ⟨absorbed, blocks, advances, selected, pairs, habs, hdecode, hafter, hlen, hfunctional⟩

#print axioms squeeze_call_functional
#print axioms advance_call_functional
#print axioms digestPair_functional
#print axioms queries_success_pairs_functional_full
#print axioms queries_success_pairs_functional

end AspisR1PublicPreparation.Query31SourceSchedule
end
