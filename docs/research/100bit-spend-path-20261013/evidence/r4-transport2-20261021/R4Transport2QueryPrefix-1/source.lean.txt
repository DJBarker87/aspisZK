import R4Transport2OpeningChain
import R4Transport2ScanComposition

/-! Exact selected-state composition of an eagerly materialized eight-pair
query chain. The scan relation is the single-step packet's reference driver. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.R4Transport2QueryPrefix
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.SqueezeOracleBridge
open TranscriptStep SourceDigestAddresses

abbrev p := SelectedTranscriptParams.params

def pairs (blocks states : Nat → State) : List (State × State) :=
  (List.range 8).map (fun k => (blocks k,states (k+1)))

/-- All potential pairs are read, but the sampler carries the selected one. -/
theorem query_chain (H : Bytes → State) (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message) (b : SelectedTranscriptParams.Message)
    (hm : LiteralTranscript.erase m = .payload b)
    (blocks states : Nat → State)
    (ha : H (RawSamplerSuffixCorrespondence.absorption P 31 b).toBytes = states 0)
    (hs : ∀ k < 8, states (k+1) = H (advanceA p (states k)).toBytes)
    (hb : ∀ k < 8, blocks k = H (squeezeA p (states k)).toBytes) :
    (eval (fun a : Addr SelectedTranscriptParams.L => H a.toBytes)
      (LiteralTranscript.samp 31 P m).toProgram).2 =
    UnifiedSampler.liftQuery (R4Transport2ScanComposition.pairsRun R0C.V3.Q22.q0
      (pairs blocks states) (states 0)) := by
  rw [RawSamplerSuffixCorrespondence.query_correspondence _ P m b hm]
  have hstates : ∀ k, k ≤ 8 →
      QuerySampler.state p (fun a => H a.toBytes) (states 0) k = states k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      simp only [QuerySampler.state]
      rw [ih (by omega), hs k (by omega)]
  have hadv : QueryStateList.advances
      (QuerySampler.state p (fun a => H a.toBytes) (states 0)) 8 =
      (pairs blocks states).map Prod.snd := by
    simp only [QueryStateList.advances, pairs, List.map_map]
    apply List.map_congr_left
    intro k hk
    exact hstates (k+1) (by have := List.mem_range.mp hk; omega)
  have hblocks : QueryStateList.blocks p (fun a => H a.toBytes)
      (QuerySampler.state p (fun a => H a.toBytes) (states 0)) 8 =
      (pairs blocks states).map Prod.fst := by
    simp only [QueryStateList.blocks, pairs, List.map_map]
    apply List.map_congr_left
    intro k hk
    rw [hstates k (by have := List.mem_range.mp hk; omega)]
    exact (hb k (List.mem_range.mp hk)).symm
  simp only [ha, QueryFirstRead.result]
  rw [hadv, hblocks]
  have hlen : (pairs blocks states).length = 8 := by simp [pairs]
  rw [R4Transport2ScanComposition.eight_pairs_selected _ _ hlen]
  rfl

/-- Apply the preceding theorem to actual source Digest32 successes, with
source and model absorb preimages already identified. No state distinctness,
oracle injectivity or equality with the eighth advance is postulated. -/
theorem source_query_chain {Hash : Type} (D : aspis_core.Digest32 Hash)
    (hash : Hash) (H : Bytes → State) (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message) (b : SelectedTranscriptParams.Message)
    (hm : LiteralTranscript.erase m = .payload b)
    (blocks states : Nat → Bytes32)
    (ha : H (RawSamplerSuffixCorrespondence.absorption P 31 b).toBytes = decodeState (states 0))
    (hs : ∀ k < 8, D.digest hash (readParts (states k) 2#u8) = ok (states (k+1)))
    (hb : ∀ k < 8, D.digest hash (readParts (states k) 1#u8) = ok (blocks k))
    (hdigest : ∀ hash parts out, D.digest hash parts = ok out →
      decodeState out = H (flatten parts)) :
    (eval (fun a : Addr SelectedTranscriptParams.L => H a.toBytes)
      (LiteralTranscript.samp 31 P m).toProgram).2 =
    UnifiedSampler.liftQuery (R4Transport2ScanComposition.pairsRun R0C.V3.Q22.q0
      (pairs (fun k => decodeState (blocks k)) (fun k => decodeState (states k)))
      (decodeState (states 0))) := by
  apply query_chain H P m b hm _ _ ha
  · intro k hk
    rw [← SourceDigestAddresses.advance_address p (states k)]
    exact hdigest hash _ _ (hs k hk)
  · intro k hk
    rw [← SourceDigestAddresses.squeeze_address p (states k)]
    exact hdigest hash _ _ (hb k hk)

#print axioms query_chain
#print axioms source_query_chain
end AspisR1PublicPreparation.R4Transport2QueryPrefix
end
