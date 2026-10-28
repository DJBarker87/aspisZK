import NBL_ScalarConstruct
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBR_BlockConstruct
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NBL_BlockTrace

/-- The infallible native Digest32 interface, expressed on the SAME digest
handle and ordered parts. It does not select outputs or a preparation run. -/
def Total {H : Type} (D : aspis_core.Digest32 H) : Prop :=
  ∀ (hash : H) (parts : Slice (Slice U8)), ∃ reply, D.digest hash parts=ok reply

/-- Construct the three chronological observations from infallibility. -/
theorem block {H : Type} (D : aspis_core.Digest32 H) (total : Total D)
    (before : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (bound : row.val≤95) : Nonempty (Block D before row payload) := by
  obtain ⟨tag,tagCall,tagValue⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=160#u8) (y:=row) (by scalar_tac))
  obtain ⟨absorbed,absorbCall⟩ := total before.hash (NBA_Transcript.absorbParts before.state tag payload)
  obtain ⟨value,readCall⟩ := total before.hash (NBA_Transcript.readParts absorbed 1#u8)
  obtain ⟨final,advanceCall⟩ := total before.hash (NBA_Transcript.readParts absorbed 2#u8)
  exact ⟨⟨tag,tagCall,absorbed,value,final,absorbCall,readCall,advanceCall⟩⟩

/-- No successful scalar result or preselected block trace is an input. -/
theorem scalar {H : Type} (D : aspis_core.Digest32 H) (total : Total D)
    (before : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (nonzero : Bool) (bound : row.val≤95) :
    Nonempty (Scalar D before row payload nonzero) := by
  obtain ⟨b⟩ := block D total before row payload bound
  obtain ⟨s,_⟩ := NBL_ScalarConstruct.source D before row payload nonzero b
  exact ⟨s⟩

/-- Determinism identifies every later returned block with THIS construction. -/
theorem returned {H : Type} (D : aspis_core.Digest32 H) (total : Total D)
    (before after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (value : Bytes32) (bound : row.val≤95)
    (call : transcript.Transcript.block D before row payload=ok (value,after)) :
    ∃ b : Block D before row payload, b.value=value ∧ b.after=after := by
  obtain ⟨b⟩ := block D total before row payload bound
  have same := Result.ok.inj ((block_result D before row payload b).symm.trans call)
  exact ⟨b,(Prod.mk.inj same).1,(Prod.mk.inj same).2⟩

#print axioms block
#print axioms scalar
#print axioms returned
end AspisR1.NBR_BlockConstruct
end
