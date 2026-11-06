import NJS_Extract.Funs
import NJS_DigestLeaves
import Port4B_LeafCode
set_option autoImplicit false
noncomputable section
namespace NJS_BatchLeaf
open Aeneas Aeneas.Std Result
open AspisR1

def refDigest {H : Type} (d : NJS_Extract.aspis_core.digest.Digest32 H) :
 NDH_TranscriptReference.NDH_DigestRef H := ⟨d.coremarkerCopyInst,d.digest⟩

def modelDigest {H : Type} (d : NJS_Extract.aspis_core.digest.Digest32 H) :
 AspisR1Stage2.aspis_core.digest.Digest32 H := ⟨d.coremarkerCopyInst,d.digest⟩

def privateLeaf {H : Type} (d : NJS_Extract.aspis_core.digest.Digest32 H) (hash : H)
 (tag : U8) (value : Slice U8) (salt : Array U8 32#usize) : Result (Array U8 32#usize) :=
 NDH_TranscriptReference.leaf_ref (refDigest d) hash tag value salt

#print core.array.TryFromArrayCopySlice.try_from
#print core.result.Result.unwrap
#print axioms privateLeaf
end NJS_BatchLeaf
