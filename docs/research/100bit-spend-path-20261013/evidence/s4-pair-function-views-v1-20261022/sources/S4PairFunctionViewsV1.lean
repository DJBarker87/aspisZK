import S4SourcePairsToFunctionsV1
import S4QueryArrayViewsV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result WP
namespace AspisR1.S4PairFunctionViewsV1
open AspisR1PublicPreparation
open AspisR1PublicPreparation.TranscriptStep
open AspisR1PublicPreparation.Query31SourceSchedule
open AspisR1.S4SourcePairsToFunctionsV1
open AspisV8R19.SqueezeOracleBridge

private theorem successful_index8_value {A : Type}
    (xs : Array A 8#usize) (i : Fin 8) (x : A)
    (h : Array.index_usize xs (index8 i.val i.isLt) = .ok x) :
    xs.val[i.val]'(by scalar_tac) = x := by
  have hiv : (index8 i.val i.isLt).val = i.val := by simp [index8]
  have hlen : (index8 i.val i.isLt).val < xs.length := by
    simpa [hiv,xs.property] using i.isLt
  obtain ⟨v,hv,hget⟩ := WP.spec_imp_exists
    (Array.index_usize_spec xs (index8 i.val i.isLt) hlen)
  have heq : v = x := Result.ok.inj (hv.symm.trans h)
  have hx := heq.symm.trans hget
  simpa only [hiv] using hx.symm

/-- The exact pair materialization suffices to identify both array lists with
pair-indexed functions. No digest law, state chain, or extra array alignment
is assumed; the function views only use the materialized eight slots. -/
theorem materialized_pair_function_views
    {Hash : Type} {D : aspis_core.Digest32 Hash} {hash : Hash}
    (pairs : List (DigestPair D hash)) (initial : Bytes32)
    (blocks advances : Array (Array U8 32#usize) 8#usize)
    (hmaterial : materializedOutputs pairs blocks advances) :
    blocks.val.map decodeState = (List.range 8).map
      (fun k => decodeState (sourcePairBlocks pairs initial k)) ∧
    advances.val.map decodeState = (List.range 8).map
      (fun k => decodeState (sourcePairStates pairs initial (k+1))) := by
  have hat : ∀ i : Fin 8,
      decodeState (blocks.val[i.val]'(by scalar_tac)) =
        decodeState (sourcePairBlocks pairs initial i.val) ∧
      decodeState (advances.val[i.val]'(by scalar_tac)) =
        decodeState (sourcePairStates pairs initial (i.val+1)) := by
    intro i
    obtain ⟨pair,hpair,hblock,hadvance⟩ := hmaterial i.val i.isLt
    have hb := successful_index8_value blocks i pair.squeeze.output hblock
    have ha := successful_index8_value advances i pair.advance.output hadvance
    have hbf : sourcePairBlocks pairs initial i.val = pair.squeeze.output := by
      simp [sourcePairBlocks,hpair]
    have haf : sourcePairStates pairs initial (i.val+1) = pair.advance.output := by
      simp [sourcePairStates,hpair]
    constructor
    · rw [hb,hbf]
    · rw [ha,haf]
  constructor
  · apply List.ext_getElem
    · simp [blocks.property]
    · intro n hleft _hright
      have hn : n < 8 := by simpa [List.length_map,blocks.property] using hleft
      simpa only [List.getElem_map,List.getElem_range] using (hat ⟨n,hn⟩).1
  · apply List.ext_getElem
    · simp [advances.property]
    · intro n hleft _hright
      have hn : n < 8 := by simpa [List.length_map,advances.property] using hleft
      simpa only [List.getElem_map,List.getElem_range] using (hat ⟨n,hn⟩).2

#print axioms materialized_pair_function_views
end AspisR1.S4PairFunctionViewsV1
end
