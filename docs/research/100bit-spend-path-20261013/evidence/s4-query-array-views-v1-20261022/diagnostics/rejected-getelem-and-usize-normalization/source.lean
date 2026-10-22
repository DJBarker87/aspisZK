import Query31MathematicalSchedule
import R1QueryStateList
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result WP
namespace AspisR1.S4QueryArrayViewsV1
open AspisR1PublicPreparation
open AspisR1PublicPreparation.TranscriptStep
open AspisR1PublicPreparation.Query31SourceSchedule
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep FS2.Duplex

private theorem successful_index8_value {A : Type}
    (xs : Array A 8#usize) (i : Fin 8) (x : A)
    (h : Array.index_usize xs (index8 i.val i.isLt) = .ok x) :
    xs.val[i.val]'(by scalar_tac) = x := by
  have hiv : (index8 i.val i.isLt).val = i.val := by
    simp [index8]
  have hlen : (index8 i.val i.isLt).val < xs.length := by
    simpa [hiv,xs.property] using i.isLt
  obtain ⟨v,hv,hget⟩ := WP.spec_imp_exists
    (Array.index_usize_spec xs (index8 i.val i.isLt) hlen)
  have heq : v = x := Result.ok.inj (hv.symm.trans h)
  have hx := heq.symm.trans hget
  simpa only [hiv] using hx.symm

/-- Exact decoded list views of the eight source-materialized digest pairs.
All per-address values are derived from existing pair witnesses, not supplied
as new equations about array entries. -/
theorem materialized_pair_views
    {Hash M Cv : Type} {L : Nat}
    {D : aspis_core.Digest32 Hash} {hash : Hash}
    (p : Params M Cv L) (H : Addr L → State) (start : State)
    (pairs : List (DigestPair D hash))
    (blockArr advanceArr : Array (Array U8 32#usize) 8#usize)
    (hmaterial : materializedOutputs pairs blockArr advanceArr)
    (hlen : pairs.length = 8)
    (hstates : pairs.map (fun pair => decodeState pair.state) =
      (List.range pairs.length).map (fun n => QuerySampler.state p H start n))
    (hfunctional : ∀ pair ∈ pairs,
      decodeState pair.squeeze.output = H (squeezeA p (decodeState pair.state)) ∧
      decodeState pair.advance.output = H (advanceA p (decodeState pair.state))) :
    blockArr.val.map decodeState =
      QueryStateList.blocks p H (QuerySampler.state p H start) 8 ∧
    advanceArr.val.map decodeState =
      QueryStateList.advances (QuerySampler.state p H start) 8 := by
  have hat : ∀ i : Fin 8,
      decodeState (blockArr.val[i.val]'(by scalar_tac)) =
        H (squeezeA p (QuerySampler.state p H start i.val)) ∧
      decodeState (advanceArr.val[i.val]'(by scalar_tac)) =
        QuerySampler.state p H start (i.val+1) := by
    intro i
    obtain ⟨pair,hpair,hblock,hadvance⟩ := hmaterial i.val i.isLt
    have hmem : pair ∈ pairs := List.mem_of_getElem? hpair
    have hsi := congrArg (fun xs : List State => xs[i.val]?) hstates
    have hs : decodeState pair.state = QuerySampler.state p H start i.val := by
      simpa [hpair,hlen,i.isLt] using hsi
    have hb := successful_index8_value blockArr i pair.squeeze.output hblock
    have ha := successful_index8_value advanceArr i pair.advance.output hadvance
    constructor
    · rw [hb,(hfunctional pair hmem).1,hs]
    · rw [ha,(hfunctional pair hmem).2,hs]
      rfl
  constructor
  · apply List.ext_getElem
    · simp [blockArr.property, QueryStateList.blocks]
    · intro n hleft hright
      have hn : n < 8 := by simpa only [List.length_map,blockArr.property] using hleft
      simpa only [List.getElem_map, QueryStateList.blocks, List.getElem_range] using (hat ⟨n,hn⟩).1
  · apply List.ext_getElem
    · simp [advanceArr.property, QueryStateList.advances]
    · intro n hleft hright
      have hn : n < 8 := by simpa only [List.length_map,advanceArr.property] using hleft
      simpa only [List.getElem_map, QueryStateList.advances, List.getElem_range] using (hat ⟨n,hn⟩).2
#print axioms materialized_pair_views
end AspisR1.S4QueryArrayViewsV1
end
