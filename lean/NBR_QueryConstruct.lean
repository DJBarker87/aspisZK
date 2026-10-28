import NBR_MaterialConstruct
import NBL_QueryTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBR_QueryConstruct
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NBL_BlockTrace

/-- The decoder starts from the fixed installed empty state; its invariant
is proved here, rather than requested from the enclosing caller. -/
theorem initial : Query31ExplicitListLoop.validState
    Query31ConcreteDriverTraceFacts.sourceDefaultState := by
  apply Query31ExplicitListLoop.validState_of_bounds <;> decide

/-- Construct the exact eager materialization AND first-stop scanner trace
on the same state carrier, for every digest and final-message input. -/
theorem source {H : Type} (D : aspis_core.Digest32 H) (total : NBR_BlockConstruct.Total D)
    (before : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (bound : row.val≤95) : Nonempty (NBL_QueryTrace.Trace D before row payload) := by
  obtain ⟨tag,tagCall,tagValue⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=160#u8) (y:=row) (by scalar_tac))
  obtain ⟨absorbed,absorbCall⟩ := total before.hash (NBA_Transcript.absorbParts before.state tag payload)
  obtain ⟨pairs⟩ := NBR_MaterialConstruct.source D total before.hash absorbed
  obtain ⟨result,walk⟩ := NBL_QueryWalk.construct pairs.advances 7#usize
    (pairs.blocks.val.zip [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize])
    Query31ConcreteDriverTraceFacts.sourceDefaultState initial
  exact ⟨⟨tag,tagCall,absorbed,absorbCall,pairs,result,walk⟩⟩

#print axioms initial
#print axioms source
end AspisR1.NBR_QueryConstruct
end
