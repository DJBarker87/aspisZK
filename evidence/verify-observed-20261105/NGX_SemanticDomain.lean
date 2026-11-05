import NGX_SemanticSample
import NFW_TranscriptDomain
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
namespace AspisR1.NGX_SemanticDomain
abbrev Bytes32 := NGX_SemanticSample.Bytes32

theorem arithmetic (row : U8) (bound : row.val≤26) :
 ∃ tag next, (160#u8+row : Result U8)=ok tag ∧
   (row+1#u8 : Result U8)=ok next ∧ tag.val=160+row.val ∧ next.val=row.val+1 := by
 obtain ⟨tag,htag,tvalue⟩ := NFW_TranscriptDomain.tag row (by omega)
 have spec : (row+1#u8 : Result U8) ⦃ z => z.val=row.val+1 ⦄ := by
  apply UScalar.add_spec
  scalar_tac
 obtain ⟨next,hnext,nvalue⟩ := WP.spec_imp_exists spec
 exact ⟨tag,next,htag,hnext,tvalue,nvalue⟩

/-- Returning digest is the accepted runtime row. No success of the semantic
callee, sampled challenge, or chosen state is a hypothesis. -/
theorem total {H : Type} (D : aspis_core.Digest32 H)
 (oracle : H→Slice (Slice U8)→Bytes32)
 (returning : ∀ h p,D.digest h p=ok (oracle h p))
 (self : r1_wire.SemanticTranscript H) (row : U8) (framed : Slice U8)
 (bound : row.val≤26) :
 ∃ out after, r1_wire.SemanticTranscript.sample_block_validated D self row framed=ok (out,after) ∧
 ((row≠self.next_row ∧ out=.Err (.RowOrder self.next_row row) ∧ after=self) ∨
  (row=self.next_row ∧ ∃ tag next,
   (160#u8+row : Result U8)=ok tag ∧ (row+1#u8 : Result U8)=ok next ∧
   let absorbed := oracle self.hash (NGX_SemanticSample.absorbParts self.state tag framed)
   let block := oracle self.hash (NGX_SemanticSample.readParts absorbed 1#u8)
   let final := oracle self.hash (NGX_SemanticSample.readParts absorbed 2#u8)
   out=.Ok block ∧ after={state:=final,hash:=self.hash,next_row:=next})) := by
 by_cases same : row=self.next_row
 · obtain ⟨tag,next,htag,hnext,_,_⟩ := arithmetic row bound
   let absorbed := oracle self.hash (NGX_SemanticSample.absorbParts self.state tag framed)
   let block := oracle self.hash (NGX_SemanticSample.readParts absorbed 1#u8)
   let final := oracle self.hash (NGX_SemanticSample.readParts absorbed 2#u8)
   refine ⟨.Ok block,{state:=final,hash:=self.hash,next_row:=next},?_,Or.inr ?_⟩
   · exact NGX_SemanticSample.returned D self row tag next framed absorbed block final same htag
       (by simpa only [←same] using hnext) (returning _ _) (returning _ _) (returning _ _)
   · exact ⟨same,tag,next,htag,hnext,rfl,rfl⟩
 · exact ⟨.Err (.RowOrder self.next_row row),self,
     NGX_SemanticSample.rejected D self row framed same,Or.inl ⟨same,rfl,rfl⟩⟩
#print axioms arithmetic
#print axioms total
end AspisR1.NGX_SemanticDomain
