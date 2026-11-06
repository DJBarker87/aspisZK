import NJZ_EmptyTree
set_option autoImplicit false
noncomputable section
namespace NJZ_TreeParent
open Aeneas Aeneas.Std Result
open NJZ_EmptyTree

/-- Child's exact seeded permutation/projection reply, as CLOSED TX1:305. -/
def reply (left right : Digest) : Digest := fun i=>
 NJP_PermutationPacket.model (NJE_CompressSeed.seed left right) ⟨i.val,by omega⟩

/-- Transcription of NJZ_native::tree_parent: SAME left/right argument values,
full arbitrary digest reply, one child call and immutable inputs. -/
structure Cut (left right seenLeft seenRight returned out : Digest) (calls : Nat) : Prop where
 left : seenLeft=left
 right : seenRight=right
 output : out=returned
 count : calls=1

/-- The CLOSED compression theorem is instantiated internally at the SAME
arguments; its entire Result is used, not a child-success/root-output premise. -/
theorem source (left right seenLeft seenRight out : Digest) (calls : Nat)
 (hl : Canonical left) (hr : Canonical right)
 (cut : Cut left right seenLeft seenRight (reply seenLeft seenRight) out calls) :
 out=parent left right ∧ calls=1 ∧ Canonical out := by
 have child := NJP_CompressionPacket.TX1_305 left right hl hr
  (NJE_CompressSeed.seed left right) (reply left right) 1
  {seed:=rfl,call_count:=rfl,output:=fun _=>rfl}
 have value : out=parent left right := by
  rw [cut.output,cut.left,cut.right]
  exact child.1
 exact ⟨value,cut.count,by rw [value];exact parent_canonical left right⟩

#print source
#print axioms source
end NJZ_TreeParent
