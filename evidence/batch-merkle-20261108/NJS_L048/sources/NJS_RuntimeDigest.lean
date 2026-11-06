import NJS_Extract.Types
import NDH_HashBridge
import Port4B_LeafCode
set_option autoImplicit false
noncomputable section
namespace NJS_RuntimeDigest
open Aeneas Aeneas.Std Result AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Concrete interpretation of the existing runtime SHA=H row.
H is the headline hash parameter; no arbitrary operation dictionary is retained. -/
def backend (H : Bytes→State) : NJS_Extract.aspis_core.digest.Digest32 Unit where
 coremarkerCopyInst := core.marker.CopyUnit
 digest := fun _ parts => ok (MultiproofConePhysicalTransport.rawOracle H parts)

def reference (H : Bytes→State) : NDH_TranscriptReference.NDH_DigestRef Unit :=
 ⟨(backend H).coremarkerCopyInst,(backend H).digest⟩

def stage (H : Bytes→State) : AspisR1Stage2.aspis_core.digest.Digest32 Unit :=
 ⟨(backend H).coremarkerCopyInst,(backend H).digest⟩

theorem input (p : Slice (Slice U8)) :
 NDH_HashBridge.input p=CheckpointBytes5Effect.flatten p := by rfl

theorem realization (H : Bytes→State) (p : Slice (Slice U8)) :
 (reference H).digest () p=ok (CheckpointBytes5Effect.encodeState (H (NDH_HashBridge.input p))) := by rfl

theorem leaf (H : Bytes→State) (tag : U8) (value : Slice U8) (salt : Array U8 32#usize) :
 NDH_TranscriptReference.leaf_ref (reference H) () tag value salt =
 ok (CheckpointBytes5Effect.encodeState (H (Merkle32Leaf.leafInput (NDH_MerkleGrammar.byte tag)
   (value.val.map NDH_MerkleGrammar.byte) (salt.val.map NDH_MerkleGrammar.byte)))) :=
 NDH_HashBridge.leaf (reference H) () (fun bytes=>ok (CheckpointBytes5Effect.encodeState (H bytes)))
   (realization H) tag value salt

theorem parent (H : Bytes→State) (children : Array (Array U8 32#usize) 8#usize) :
 NDH_TranscriptReference.parent_ref (reference H) () children=
 ok (CheckpointBytes5Effect.encodeState (H (Merkle32Path.nodeInput (NDH_MerkleGrammar.children children)))) :=
 NDH_HashBridge.parent (reference H) () (fun bytes=>ok (CheckpointBytes5Effect.encodeState (H bytes)))
   (realization H) children
#check leaf
#check parent
#print axioms input
#print axioms realization
#print axioms leaf
#print axioms parent
end NJS_RuntimeDigest
