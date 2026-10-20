import PreparedPost25QueryRhoCaller
import AspisV8R19.Q22WordScan

open Aeneas Aeneas.Std Result
open Query31ExplicitListLoop Query31ExplicitScanBody
open Query31ModelDriverChain Query31ConcreteWordsDriverChain
open AspisR1QueryScanUnrolled.r0_transcript

open AspisR1PublicPreparation.OpeningRun
open AspisR1PublicPreparation.PreparedReachability
open AspisR1PublicPreparation.SamplerTransport

set_option autoImplicit false
noncomputable section

namespace AspisR1PublicPreparation.PreparedQueryLegalRhoBridge

private theorem queryMaskWord_lt (w : Std.U32) :
    (queryMaskWord w).val < 262144 := by
  change (w.bv &&& (262143#u32).bv).toNat < 262144
  rw [BitVec.toNat_and]
  change w.val &&& 262143 < 262144
  exact Nat.lt_succ_of_le Nat.and_le_right

private theorem keep_nodup (xs : List Nat) (x : Nat) (h : xs.Nodup) :
    AspisV8R19.Q22WordScan.keep xs x |>.Nodup := by
  by_cases hx : x ∈ xs
  · simp [AspisV8R19.Q22WordScan.keep, hx, h]
  · rw [AspisV8R19.Q22WordScan.keep, if_neg hx]
    rw [List.nodup_append]
    refine ⟨h, by simp, ?_⟩
    intro a ha b hb hab
    simp only [List.mem_singleton] at hb
    subst b
    apply hx
    rw [hb] at ha
    exact ha

private theorem keep_range (xs : List Nat) (x : Nat)
    (hxs : ∀ y ∈ xs, y < 262144) (hx : x < 262144) :
    ∀ y ∈ AspisV8R19.Q22WordScan.keep xs x, y < 262144 := by
  by_cases hmem : x ∈ xs
  · simpa [AspisV8R19.Q22WordScan.keep, hmem] using hxs
  · intro y hy
    rw [AspisV8R19.Q22WordScan.keep, if_neg hmem] at hy
    rw [List.mem_append] at hy
    rcases hy with hy | hy
    · exact hxs y hy
    · simp only [List.mem_singleton] at hy
      simpa [hy] using hx

private theorem scan_preserves_legal (s : AspisV8R19.Q22WordScan.ScanState) (xs : List Nat)
    (hs : s.accepted.Nodup ∧ ∀ x ∈ s.accepted, x < 262144)
    (hxs : ∀ x ∈ xs, x < 262144) :
    ((AspisV8R19.Q22WordScan.scan s xs).1.accepted).Nodup ∧
      ∀ x ∈ (AspisV8R19.Q22WordScan.scan s xs).1.accepted, x < 262144 := by
  induction xs generalizing s with
  | nil => simpa [AspisV8R19.Q22WordScan.scan] using hs
  | cons x xs ih =>
      by_cases hstop : s.accepted.length = 22 ∨ s.draws = 64
      · simpa [AspisV8R19.Q22WordScan.scan, hstop] using hs
      · simp only [AspisV8R19.Q22WordScan.scan, if_neg hstop]
        apply ih
        · exact ⟨keep_nodup s.accepted x hs.1,
            keep_range s.accepted x hs.2 (hxs x (by simp))⟩
        · intro y hy
          exact hxs y (List.mem_cons_of_mem x hy)

private theorem queryWords_bounded
    {blocks : Array (Array Std.U8 32#usize) 8#usize}
    (e : BlockEvidence actualQueryWords blocks)
    (he : e.words.val = (List.range 8).map
      (fun j => queryMaskWord (blockRankWord e.bytes j))) :
    ∀ x ∈ e.words.val.map (fun w => w.val), x < 262144 := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨w, hw, rfl⟩
  have hword : ∀ w ∈ e.words.val, w.val < 262144 := by
    intro w hw
    rw [he] at hw
    rcases List.mem_map.mp hw with ⟨j, hj, rfl⟩
    exact queryMaskWord_lt _
  exact hword w hw

private theorem chain_legal
    (blocks : Array (Array Std.U8 32#usize) 8#usize)
    (s0 sf : QueryScan)
    (evidence : List (BlockEvidence actualQueryWords blocks))
    (hchain : Q22ScanChain actualQueryWords blocks s0 evidence sf)
    (hwords : ∀ e ∈ evidence, e.words.val = (List.range 8).map
      (fun j => queryMaskWord (blockRankWord e.bytes j)))
    (hstart : (Query31ExplicitScanBody.q22StateOf s0).accepted.Nodup ∧
      ∀ x ∈ (Query31ExplicitScanBody.q22StateOf s0).accepted, x < 262144) :
    (Query31ExplicitScanBody.q22StateOf sf).accepted.Nodup ∧
      ∀ x ∈ (Query31ExplicitScanBody.q22StateOf sf).accepted, x < 262144 := by
  revert hstart hwords
  induction hchain with
  | nil s hs =>
      intro hwords hstart
      exact hstart
  | @cons s s' sf e rest hs hcall hsemantic hvalid htail ih =>
      intro hwords hstart
      have hsafe := scan_preserves_legal (Query31ExplicitScanBody.q22StateOf s)
        (e.words.val.map (fun x => x.val)) hstart
        (queryWords_bounded e (hwords e (by simp)))
      have hnext :
          (Query31ExplicitScanBody.q22StateOf s').accepted.Nodup ∧
            ∀ x ∈ (Query31ExplicitScanBody.q22StateOf s').accepted,
              x < 262144 := by
        rw [hsemantic] at hsafe
        exact hsafe
      have hwordsRest : ∀ e' ∈ rest, e'.words.val = (List.range 8).map
          (fun j => queryMaskWord (blockRankWord e'.bytes j)) := by
        intro e' he'
        exact hwords e' (List.mem_cons_of_mem _ he')
      exact ih hwordsRest hnext

private def coordinatesOfList (xs : List Nat) (hlen : xs.length = 22)
    (hbound : ∀ x ∈ xs, x < 262144) : Fin 22 → Fin 262144 :=
  fun i => ⟨xs.get ⟨i.val, by omega⟩,
    hbound _ (List.get_mem xs ⟨i.val, by omega⟩)⟩

private theorem coordinatesOfList_injective (xs : List Nat)
    (hlen : xs.length = 22) (hbound : ∀ x ∈ xs, x < 262144)
    (hnodup : xs.Nodup) :
    Function.Injective (coordinatesOfList xs hlen hbound) := by
  intro i j hij
  have hval : xs.get ⟨i.val, by omega⟩ = xs.get ⟨j.val, by omega⟩ :=
    congrArg Fin.val hij
  have hidx : (⟨i.val, by omega⟩ : Fin xs.length) =
      ⟨j.val, by omega⟩ :=
    (List.nodup_iff_injective_get.mp hnodup) hval
  have hidxval : i.val = j.val :=
    congrArg (fun k : Fin xs.length => k.val) hidx
  exact Fin.ext hidxval

private theorem coordinatesOfList_enum (xs : List Nat)
    (hlen : xs.length = 22) (hbound : ∀ x ∈ xs, x < 262144) :
    List.ofFn (fun i : Fin 22 => (coordinatesOfList xs hlen hbound i).val) = xs := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using hlen.symm
  · intro i hi hj
    simp only [List.getElem_ofFn, coordinatesOfList, List.get_eq_getElem]

/-- A successful concrete first-stop Query31 execution returns the exact
ordered, distinct 18-bit query list used by the retained finite query type. -/
theorem schedule_output_is_legal_query
    {H M Cv : Type} {L : Nat}
    (D : aspis_core.Digest32 H) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice Std.U8) (root : TranscriptStep.Bytes32) (length : Std.U32)
    (self after : transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 →
      Result AspisR1PublicPreparation.aspis_core.field.WideExact)
    (out : Array Std.U32 22#usize)
    (hsuccess : QueriesModel.queries
      (Query31ConcreteMaterializedSchedule.concreteBoundaries
        Query31ConcreteDriverTraceFacts.sourceDefaultState embed)
      D self row payload = .ok (.Ok out, after)) :
    ∃ q : Fin 22 → Fin 262144,
      Function.Injective q ∧
      List.ofFn (fun i : Fin 22 => (q i).val) = out.val.map
        (fun w => w.val) := by
  obtain ⟨absorbed, blocks, advances, selected', pairs, evidence, sf,
      habs, hmaterial, hpaircount, hstates, hafter, hfunctional,
      hchain, hlenEvidence, hvalidFinal, hwords,
      stopIndex, htrace, hcount, hbuffer, hfinish, hadvance, hindexBound⟩ :=
    Query31ConcreteMaterializedScheduleFull.successful_default_concrete_materialized_query_schedule
      D p pubInput root length self after row payload embed out hsuccess
  have hstart :
      (Query31ExplicitScanBody.q22StateOf
        Query31ConcreteDriverTraceFacts.sourceDefaultState).accepted.Nodup ∧
      ∀ x ∈ (Query31ExplicitScanBody.q22StateOf
        Query31ConcreteDriverTraceFacts.sourceDefaultState).accepted,
          x < 262144 := by
    rw [Query31ConcreteDriverTraceFacts.sourceDefaultState_maps_to_empty_q22]
    simp
  have hfinal := chain_legal blocks Query31ConcreteDriverTraceFacts.sourceDefaultState
    sf evidence hchain hwords hstart
  have hprefix : Query31ExplicitScanBody.acceptedPrefix sf =
      out.val.map (fun w => w.val) := by
    unfold Query31ExplicitScanBody.acceptedPrefix
    rw [hbuffer]
    have hcountval : sf.accepted_len.val = 22 := by
      have h := congrArg UScalar.val hcount
      simpa [UScalar.ofNatCore_val_eq] using h
    have houtlen : out.val.length = 22 := by simpa using out.property
    simp [hcountval, houtlen]
  have hn : (out.val.map (fun w => w.val)).Nodup := by
    simpa [Query31ExplicitScanBody.q22StateOf, hprefix] using hfinal.1
  have hb : ∀ x ∈ out.val.map (fun w => w.val), x < 262144 := by
    simpa [Query31ExplicitScanBody.q22StateOf, hprefix] using hfinal.2
  have hlen : (out.val.map (fun w => w.val)).length = 22 := by
    simpa using out.property
  let q := coordinatesOfList (out.val.map (fun w => w.val)) hlen hb
  exact ⟨q, coordinatesOfList_injective _ hlen hb hn,
    coordinatesOfList_enum _ hlen hb⟩

/-- The same successful Prepared result contains both the concrete ordered
query vector and the row-32 rho output; this packages the former as the exact
legal coordinate object consumed by residual/rank bounds. -/
theorem prepare_success_concrete_query_rho_legal
    {H M Cv : Type} {L : Nat}
    (B : PreparedModel.Boundaries)
    (D : aspis_core.Digest32 H) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice Std.U8) (root : TranscriptStep.Bytes32) (length : Std.U32)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (out : verifier.Prepared)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 →
      Result AspisR1PublicPreparation.aspis_core.field.WideExact)
    (hfolds : transport.Variant.folds v.variant = .ok 2#usize)
    (hprep : PreparedModel.prepare
      (OpeningRun.bindQueries B (Query31ConcreteMaterializedSchedule.concreteBoundaries
        Query31ConcreteDriverTraceFacts.sourceDefaultState embed))
      D sem v hash = .ok (.Ok out)) :
    ∃ before : transcript.Transcript H,
      ∃ queries : Array U32 22#usize,
      ∃ afterQueries last : transcript.Transcript H,
        ∃ block : Array U8 32#usize,
          ∃ q : Fin 22 → Fin 262144,
            QueriesModel.queries
              (Query31ConcreteMaterializedSchedule.concreteBoundaries
                Query31ConcreteDriverTraceFacts.sourceDefaultState embed)
              D before 31#u8 v.final_message = .ok (.Ok queries, afterQueries) ∧
            out.queries = queries ∧
            Function.Injective q ∧
            List.ofFn (fun i : Fin 22 => (q i).val) = queries.val.map
              (fun w => w.val) ∧
            transcript.Transcript.block D afterQueries 32#u8 emptyPayload =
              .ok (block, last) ∧ sampler.qm31_sample block = .ok out.rho ∧
            AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
              (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
                (toOld out.rho)) ∧
            AspisR1.ExtractedQM31SamplerCorrect.coordinates (toOld out.rho) =
              AspisR1.SamplerNatModel.qm31Digits
                (AspisR1.SourceSamplerByteRank.rank block) := by
  obtain ⟨before, queries, afterQueries, last, block,
      hquery, hreturned, hfacts, hblock, hsample, hcanonical, hcoordinates⟩ :=
    Post25QueryRhoCaller.prepare_success_concrete_query_rho B D p pubInput root
      length sem v hash out embed hfolds hprep
  obtain ⟨q, hqinj, hqenum⟩ := schedule_output_is_legal_query D p pubInput root length
    before afterQueries 31#u8 v.final_message embed queries hquery
  refine ⟨before, queries, afterQueries, last, block, q,
    hquery, hreturned, hqinj, ?_, hblock, hsample, hcanonical, hcoordinates⟩
  simpa [hreturned] using hqenum

#print axioms schedule_output_is_legal_query
#print axioms prepare_success_concrete_query_rho_legal

end AspisR1PublicPreparation.PreparedQueryLegalRhoBridge
end
