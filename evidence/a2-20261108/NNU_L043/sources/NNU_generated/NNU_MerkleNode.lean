import NNU_MerkleLeaf
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_MerkleNode
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalProgram MultiproofConePhysicalDigest
open AspisV8R19.MemoizedProgramLaw
/-- Only the actual binary node request is required. -/
theorem writer {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
 (H : MultiproofConePhysicalProgram.Address → MultiproofConePhysicalProgram.Digest)
 (law : ∀ left right, D.digest hash (parts left right)=.ok (H (parts left right)))
 (s : reference.Scratch) (left right : Array U8 32#usize) (ni cursor : Usize) (index : U32) (w : Usize) :
 (eval H (MultiproofConePhysicalProgram.writer s left right ni cursor index w)).2=
 reference.write_parent D hash s left right ni cursor index w := by
 change finish s (H (parts left right)) ni cursor index w = _
 unfold reference.write_parent
 change _ = (do let digest ← D.digest hash (parts left right); finish s digest ni cursor index w)
 rw [law]; rfl

theorem node {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
 (H : MultiproofConePhysicalProgram.Address → MultiproofConePhysicalProgram.Digest)
 (law : ∀ left right, D.digest hash (parts left right)=.ok (H (parts left right)))
 (s : reference.Scratch) (physical : Slice U8) (i w : Usize) :
 (eval H (MultiproofConePhysicalProgram.node s physical i w)).2=
 reference.binary_step D hash s physical i w := by
 simp only [MultiproofConePhysicalProgram.node,checked_result,conditional_result,writer D hash H law,eval]
 unfold reference.binary_step
 rfl
#print axioms writer
#print axioms node
end AspisR1.NNU_MerkleNode
end
