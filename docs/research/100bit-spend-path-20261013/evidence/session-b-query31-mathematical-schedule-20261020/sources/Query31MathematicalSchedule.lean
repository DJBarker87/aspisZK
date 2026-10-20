import Query31SourceOracleBridge
import R1QuerySampler

open Aeneas Aeneas.Std Result
open FS FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation.SourceDigestOracle
open AspisR1.QuerySampler
set_option autoImplicit false
noncomputable section

namespace AspisR1PublicPreparation.Query31SourceSchedule
open AspisR1PublicPreparation

/-- A list of actual source pairs follows the retained recurrence from `start`.
The recurrence uses the concrete source digest oracle supplied by the caller. -/
def alignedStates {Hash M Cv : Type} {L : Nat}
    {D : aspis_core.Digest32 Hash} {hash : Hash}
    (p : Params M Cv L) (H : Addr L → State) (start : State) :
    List (DigestPair D hash) → Prop
  | [] => True
  | pair :: rest =>
      decodeState pair.state = start ∧
      alignedStates p H (H (advanceA p start)) rest

/-- The source byte-state links, together with the actual advance digest
outputs, force every subsequent source pair to be the mathematical sampler
state at the same index. -/
theorem stateChain_alignedStates {Hash M Cv : Type} {L : Nat}
    {D : aspis_core.Digest32 Hash} {hash : Hash}
    (p : Params M Cv L) (H : Addr L → State) :
    ∀ (first : DigestPair D hash) (rest : List (DigestPair D hash)),
      stateChain (first :: rest) →
      (∀ pair ∈ first :: rest,
        decodeState pair.advance.output = H (advanceA p (decodeState pair.state))) →
      alignedStates p H (decodeState first.state) (first :: rest) := by
  intro first rest
  induction rest generalizing first with
  | nil =>
      intro _ _
      simp [alignedStates]
  | cons second tail ih =>
      intro hchain hadvance
      rcases hchain with ⟨hlink, htail⟩
      have hfirst := hadvance first (by simp)
      have hsecond : decodeState second.state = H (advanceA p (decodeState first.state)) := by
        rw [hlink]
        exact hfirst
      change decodeState first.state = decodeState first.state ∧
        alignedStates p H (H (advanceA p (decodeState first.state))) (second :: tail)
      refine ⟨rfl, ?_⟩
      have htailAligned := ih second htail (fun pair hp => hadvance pair (by simp [hp]))
      rw [hsecond] at htailAligned
      exact htailAligned

/-- The aligned source states are exactly the retained `AspisR1.QuerySampler.state`
sequence, in order. -/
theorem alignedStates_map_eq_querySampler {Hash M Cv : Type} {L : Nat}
    {D : aspis_core.Digest32 Hash} {hash : Hash}
    (p : Params M Cv L) (H : Addr L → State) (start : State)
    (pairs : List (DigestPair D hash))
    (haligned : alignedStates p H start pairs) :
    pairs.map (fun pair => decodeState pair.state) =
      (List.range pairs.length).map (fun i => AspisR1.QuerySampler.state p H start i) := by
  induction pairs generalizing start with
  | nil => rfl
  | cons first rest ih =>
      rcases haligned with ⟨hfirst, htail⟩
      simp only [List.map_cons, List.length_cons]
      rw [AspisR1.QuerySampler.map_range_succ]
      have htail' : alignedStates p H (H (advanceA p start)) rest := by
        simpa [hfirst] using htail
      simp only [AspisR1.QuerySampler.state_succ']
      change decodeState first.state :: rest.map (fun pair => decodeState pair.state) =
        start :: (List.range rest.length).map (fun k => AspisR1.QuerySampler.state p H
          (H (advanceA p start)) k)
      rw [hfirst]
      have htailMap := ih (H (advanceA p start)) htail'
      exact congrArg (List.cons start) htailMap

/-- A successful actual source query yields all eight ordered materialized
squeeze/advance pairs on the retained mathematical schedule. The decoder's
selected continuation remains its explicit output; this theorem does not
identify it with the eighth advance unless the decoder supplies that fact. -/
theorem queries_success_on_querySampler_schedule {Hash M Cv : Type} {L : Nat}
    (B : QueriesModel.Boundaries) (D : aspis_core.Digest32 Hash)
    (p : Params M Cv L) (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (self after : transcript.Transcript Hash) (row : U8) (payload : Slice U8)
    (out : Array U32 22#usize)
    (h : QueriesModel.queries B D self row payload = ok (.Ok out, after)) :
    ∃ absorbed blocks advances selected,
      ∃ pairs : List (DigestPair D absorbed.hash),
        transcript.Transcript.absorb D self row payload = ok absorbed ∧
        B.decode blocks advances = ok (.Ok (out, selected)) ∧
        after = {absorbed with state := selected} ∧
        pairs.length = 8 ∧
        materializedOutputs pairs blocks advances ∧
        pairs.map (fun pair => decodeState pair.state) =
          (List.range pairs.length).map
            (fun i => AspisR1.QuerySampler.state p
              (SourceDigestOracle.oracle D absorbed.hash pubInput root length)
              (decodeState absorbed.state) i) ∧
        (∀ pair ∈ pairs,
          decodeState pair.squeeze.output =
            SourceDigestOracle.oracle D absorbed.hash pubInput root length
              (squeezeA p (decodeState pair.state)) ∧
          decodeState pair.advance.output =
            SourceDigestOracle.oracle D absorbed.hash pubInput root length
              (advanceA p (decodeState pair.state))) := by
  obtain ⟨absorbed, blocks, advances, selected, pairs, habs, hdecode, hafter,
      hlen, hfirst, hchain, hfunctional, hmaterial⟩ :=
    queries_success_pairs_functional_full B D p pubInput root length self after row payload out h
  rcases hfirst with ⟨first, rest, hpairs, hfirstState⟩
  subst pairs
  let H : Addr L → State := SourceDigestOracle.oracle D absorbed.hash pubInput root length
  have hadvance : ∀ pair ∈ first :: rest,
      decodeState pair.advance.output = H (advanceA p (decodeState pair.state)) := by
    intro pair hmem
    exact (hfunctional pair hmem).2
  have haligned := stateChain_alignedStates p H first rest hchain hadvance
  have hmap := alignedStates_map_eq_querySampler p H (decodeState first.state) (first :: rest) haligned
  have hstart : decodeState first.state = decodeState absorbed.state := by
    exact congrArg decodeState hfirstState
  rw [hstart] at hmap
  refine ⟨absorbed, blocks, advances, selected, first :: rest, habs, hdecode, hafter,
    hlen, hmaterial, ?_, ?_⟩
  · simpa [H] using hmap
  · simpa [H] using hfunctional

#print axioms stateChain_alignedStates
#print axioms alignedStates_map_eq_querySampler
#print axioms queries_success_on_querySampler_schedule

end AspisR1PublicPreparation.Query31SourceSchedule
end
