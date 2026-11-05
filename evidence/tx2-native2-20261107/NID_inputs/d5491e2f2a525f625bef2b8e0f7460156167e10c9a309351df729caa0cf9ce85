import NHV_COMBINED_IMPORT
import Port4B_LeafCode
set_option autoImplicit false
noncomputable section
namespace NID_MerkleLeafPacket
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open CheckpointBytes5Effect

/-- The actual opening expression supplies the SAME bounded view to all three
leaf branches. Full oracle reply and ordered log are preserved, without any
assumption about digest VALUE or a successful Merkle result. -/
theorem selected {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
 (proof : Slice U8) (length : proof.val.length=57607) (index kind : Usize)
 (inside : index.val<22) (before : Log) :
 ∃ view, Port4B_Opening.opening proof index=ok view ∧ view.val.length=832 ∧
  MultiproofConeCanonical.bytesOf view.val=
   OraclePortCompactDraft.slice (MultiproofConeCanonical.bytesOf proof.val) (10055+index.val*832) 832 ∧
  erase D hash (Port4B_LeafCode.code kind view)=D.digest hash (Port4B_LeafCode.input kind view) ∧
  run D hash (Port4B_LeafCode.code kind view) before=
   (do let d←D.digest hash (Port4B_LeafCode.input kind view)
       ok (d,before++[(Port4B_LeafCode.input kind view,d)])) := by
 obtain ⟨view,read,size,value⟩ := Port4B_Opening.opening_exact proof length index inside
 have packet := Port4B_LeafCode.code_exact D hash kind view size before
 exact ⟨view,read,size,value,packet.1,packet.2⟩

/-- A failed digest has no executed suffix. The runtime abort interpretation is
retained under (an); no native Err arm or successful hash totality is invented. -/
theorem fail_no_suffix {H A : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
 (kind : Usize) (view : Slice U8) (width : view.val.length=832)
 (e : Error) (call : D.digest hash (Port4B_LeafCode.input kind view)=.fail e)
 (suffix : Digest → Code A) :
 erase D hash (Port4B_LeafCode.code kind view >>= suffix)=.fail e := by
 rw [erase_bind,(Port4B_LeafCode.code_exact D hash kind view width []).1,call]
 rfl

theorem div_no_suffix {H A : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
 (kind : Usize) (view : Slice U8) (width : view.val.length=832)
 (call : D.digest hash (Port4B_LeafCode.input kind view)=.div)
 (suffix : Digest → Code A) :
 erase D hash (Port4B_LeafCode.code kind view >>= suffix)=.div := by
 rw [erase_bind,(Port4B_LeafCode.code_exact D hash kind view width []).1,call]
 rfl
#print axioms selected
#print axioms fail_no_suffix
#print axioms div_no_suffix
end NID_MerkleLeafPacket
