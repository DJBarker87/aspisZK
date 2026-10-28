import AspisR1PublicPreparation.Funs
set_option autoImplicit false
namespace NDI_TranscriptLaw
open Aeneas Aeneas.Std Result
abbrev Bytes32 := Array U8 32#usize

def absorbParts (state : Bytes32) (tag : U8) (framed : Slice U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 3#usize [Array.to_slice state,
    Array.to_slice (Array.make 2#usize [0#u8,tag]),framed])
def taggedParts (state : Bytes32) (tag : U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 2#usize [Array.to_slice state,
    Array.to_slice (Array.make 1#usize [tag])])
def newParts (publicBytes : Slice U8) (root : Bytes32) (length : U32) : Slice (Slice U8) :=
  Array.to_slice (Array.make 5#usize [AspisR1PublicPreparation.r1_wire.DOMAIN,
    Array.to_slice (Array.make 1#usize [0#u8]),
    Array.to_slice (core.num.U32.to_le_bytes length),publicBytes,Array.to_slice root])

theorem sample {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (self : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (row tag next : U8) (framed : Slice U8) (absorbed block advanced : Bytes32)
    (same : self.next_row=row) (addTag : 160#u8+row=ok tag) (inc : row+1#u8=ok next)
    (absorb : D.digest self.hash (absorbParts self.state tag framed)=ok absorbed)
    (squeeze : D.digest self.hash (taggedParts absorbed 1#u8)=ok block)
    (advance : D.digest self.hash (taggedParts absorbed 2#u8)=ok advanced) :
    AspisR1PublicPreparation.r1_wire.SemanticTranscript.sample_block_validated D self row framed =
      ok (.Ok block,{self with state:=advanced,next_row:=next}) := by
  unfold absorbParts at absorb
  unfold taggedParts at squeeze advance
  simp only [AspisR1PublicPreparation.r1_wire.SemanticTranscript.sample_block_validated,
    same,bne_self_eq_false,Bool.false_eq_true,if_false,addTag,inc,lift,bind_tc_ok,
    absorb,squeeze,advance]

theorem rejected {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (self : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (row : U8) (framed : Slice U8) (different : row≠self.next_row) :
    AspisR1PublicPreparation.r1_wire.SemanticTranscript.sample_block_validated D self row framed =
      ok (.Err (.RowOrder self.next_row row),self) := by
  have h : (row != self.next_row)=true := bne_iff_ne.mpr different
  rw [AspisR1PublicPreparation.r1_wire.SemanticTranscript.sample_block_validated,if_pos h]

theorem sample_domain (row : U8) (bound : row.val≤26) :
    ∃ tag next : U8, 160#u8+row=ok tag ∧ row+1#u8=ok next ∧
      tag.val=160+row.val ∧ next.val=row.val+1 := by
  obtain ⟨tag,add,hTag⟩ := WP.spec_imp_exists (U8.add_spec (x:=160#u8) (y:=row) (by scalar_tac))
  obtain ⟨next,inc,hNext⟩ := WP.spec_imp_exists (U8.add_spec (x:=row) (y:=1#u8) (by scalar_tac))
  refine ⟨tag,next,add,inc,?_,?_⟩ <;> scalar_tac

#print axioms sample
#print axioms rejected
#print axioms sample_domain
end NDI_TranscriptLaw
