import NGX_StateImpl
import NGT_RuntimeDomain
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
namespace AspisR1.NGX_SemanticSample
abbrev Bytes32 := Array U8 32#usize

def absorbParts (state : Bytes32) (tag : U8) (framed : Slice U8) : Slice (Slice U8) :=
 Array.to_slice (Array.make 3#usize [Array.to_slice state,
   Array.to_slice (Array.make 2#usize [0#u8,tag]),framed])
def readParts (state : Bytes32) (tag : U8) : Slice (Slice U8) :=
 Array.to_slice (Array.make 2#usize [Array.to_slice state,
   Array.to_slice (Array.make 1#usize [tag])])

theorem rejected {H : Type} (D : aspis_core.Digest32 H)
 (self : r1_wire.SemanticTranscript H) (row : U8) (framed : Slice U8)
 (different : row ≠ self.next_row) :
 r1_wire.SemanticTranscript.sample_block_validated D self row framed =
   ok (.Err (.RowOrder self.next_row row),self) := by
 unfold r1_wire.SemanticTranscript.sample_block_validated
 simp only [bne_iff_ne]
 rw [if_pos different]

theorem returned {H : Type} (D : aspis_core.Digest32 H)
 (self : r1_wire.SemanticTranscript H) (row tag next : U8) (framed : Slice U8)
 (absorbed block final : Bytes32)
 (same : row = self.next_row)
 (htag : (160#u8+row : Result U8)=ok tag)
 (hnext : (self.next_row+1#u8 : Result U8)=ok next)
 (first : D.digest self.hash (absorbParts self.state tag framed)=ok absorbed)
 (second : D.digest self.hash (readParts absorbed 1#u8)=ok block)
 (third : D.digest self.hash (readParts absorbed 2#u8)=ok final) :
 r1_wire.SemanticTranscript.sample_block_validated D self row framed =
   ok (.Ok block,{state:=final,hash:=self.hash,next_row:=next}) := by
 subst row
 unfold r1_wire.SemanticTranscript.sample_block_validated
 simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
 simp only [lift,bind_tc_ok,htag,absorbParts,readParts] at first second third ⊢
 rw [first,bind_tc_ok,second,bind_tc_ok,third,bind_tc_ok,hnext,bind_tc_ok]

def absorbViews (state tag framed size : Nat) : List (Nat×Nat) :=
 [(state,32),(tag,2),(framed,size)]
theorem digest_domain (state tag framed size : Nat) (bound : size≤3717) :
 (absorbViews state tag framed size).length≤9 ∧
 ∀ v∈absorbViews state tag framed size,v.2≤57607 := by
 constructor
 · change 3≤9; decide
 · intro v h
   simp only [absorbViews,List.mem_cons,List.not_mem_nil,or_false] at h
   rcases h with rfl | rfl | rfl <;> dsimp <;> omega
#print axioms rejected
#print axioms returned
#print axioms digest_domain
end AspisR1.NGX_SemanticSample
