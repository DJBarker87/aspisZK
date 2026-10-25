import S1OwnedQueryPairsDriveV1
set_option autoImplicit false
namespace AspisS1OwnedQueryPairs.Model
open Aeneas Aeneas.Std Result
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

theorem pairsOf_all_length (blocks advances : Blocks) :
    (pairsOf allIndices blocks advances).length=8 := by simp [pairsOf,allIndices]

theorem pairsOf_all_blocks (blocks advances : Blocks) :
    (pairsOf allIndices blocks advances).map Prod.fst=blocks.val.map decodeState := by
  unfold pairsOf allIndices
  rw [List.map_map]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_ofFn,blocks.property]
    rfl
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_ofFn]
    rfl

theorem pairsOf_all_advances (blocks advances : Blocks) :
    (pairsOf allIndices blocks advances).map Prod.snd=advances.val.map decodeState := by
  unfold pairsOf allIndices
  rw [List.map_map]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_ofFn,advances.property]
    rfl
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_ofFn]
    rfl

theorem lastAdvance_all (blocks advances : Blocks) (fallback : State) :
    lastAdvance (pairsOf allIndices blocks advances) fallback=
      decodeState (atBlock advances 7#usize (by decide)) := by
  simp only [pairsOf,allIndices_list,List.map_cons,List.map_nil,lastAdvance]
  rfl

theorem initial_valid : Valid initial := by
  unfold Valid initial
  constructor <;> scalar_tac

theorem initial_q0 : qState initial=R0C.V3.Q22.q0 := rfl

#print axioms pairsOf_all_blocks
#print axioms pairsOf_all_advances
#print axioms lastAdvance_all
#print axioms initial_q0
end AspisS1OwnedQueryPairs.Model
