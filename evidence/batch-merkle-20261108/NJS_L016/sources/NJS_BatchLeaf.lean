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

/-- Exact successful32-byte std copy; its value is the entire source slice. -/
theorem copied (s : Slice U8) (size : s.val.length=32) :
 (do let r ← core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s
     core.result.Result.unwrap core.fmt.DebugTryFromSliceError r) =
   ok (⟨s.val,size⟩ : Array U8 32#usize) := by
 simp [core.array.TryFromArrayCopySlice.try_from,core.result.Result.unwrap,size]

/-- Complete emitted return and one ordered digest request at the cohort inputs.
The private leaf operation is instantiated, never an endpoint hypothesis. -/
theorem source {H : Type} (d : NJS_Extract.aspis_core.digest.Digest32 H) (hash : H)
 (kind : Usize) (q : Slice U8) (len : q.val.length=832) :
 NJS_Extract.verifier.candidate.batch_leaf (ok 113#u8) (ok 241#u8) privateLeaf d hash kind q =
 Port4B_LeafCode.native (modelDigest d) hash kind q := by
 rw [Port4B_LeafCode.native,(Port4B_LeafCode.code_exact (modelDigest d) hash kind q len []).1]
 have range (a b : Usize) (ha : a.val≤b.val) (hb : b.val≤832) :=
   MultiproofConeSlices.range_total q a b ha (by omega)
 have headRange (b : Usize) (hb : b.val≤832) :=
   MultiproofConeSlices.prefix_total q b (by omega)
 have cp (a b : Usize) (ha : a.val≤b.val) (hb : b.val≤832) (width : b.val-a.val=32) :
   core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 (MultiproofConeSlices.sub q a b) =
     ok (.Ok (⟨(MultiproofConeSlices.sub q a b).val,by
       rw [MultiproofConeSlices.sub_length q a b ha (by omega),width];rfl⟩ : Array U8 32#usize)) := by
   have length := MultiproofConeSlices.sub_length q a b ha (by omega)
   simp [core.array.TryFromArrayCopySlice.try_from,length,width]
 by_cases z : kind=0#usize
 · subst kind
   simp only [NJS_Extract.verifier.candidate.batch_leaf,Port4B_LeafCode.input,show (0#usize).val=0 from rfl,ite_true,
     range 608#usize 640#usize (by decide) (by decide),headRange 480#usize (by decide),
     cp 608#usize 640#usize (by decide) (by decide) (by decide),bind_tc_ok,
     core.result.Result.unwrap,privateLeaf,NDH_TranscriptReference.leaf_ref,lift,bind_tc_ok,
     Port4B_LeafCode.parts,refDigest,modelDigest,Array.to_slice,Array.make]
   rfl
 · by_cases o : kind=1#usize
   · subst kind
     simp only [NJS_Extract.verifier.candidate.batch_leaf,Port4B_LeafCode.input,
       show (1#usize).val=1 from rfl,show ¬1#usize=0#usize by decide,if_false,ite_true,
       range 640#usize 672#usize (by decide) (by decide),range 480#usize 608#usize (by decide) (by decide),
       cp 640#usize 672#usize (by decide) (by decide) (by decide),bind_tc_ok,
       core.result.Result.unwrap,privateLeaf,NDH_TranscriptReference.leaf_ref,lift,bind_tc_ok,
     Port4B_LeafCode.parts,refDigest,modelDigest,Array.to_slice,Array.make]
     rfl
   · have zv : kind.val≠0 := by intro h;exact z (UScalar.eq_of_val_eq h)
     have ov : kind.val≠1 := by intro h;exact o (UScalar.eq_of_val_eq h)
     unfold NJS_Extract.verifier.candidate.batch_leaf
     split
     · contradiction
     · contradiction
     · simp only [Port4B_LeafCode.input,if_neg z,if_neg o,
         range 800#usize 832#usize (by decide) (by decide),range 672#usize 800#usize (by decide) (by decide),
         cp 800#usize 832#usize (by decide) (by decide) (by decide),bind_tc_ok,
         core.result.Result.unwrap,privateLeaf,NDH_TranscriptReference.leaf_ref,lift,bind_tc_ok,
     Port4B_LeafCode.parts,refDigest,modelDigest,Array.to_slice,Array.make]
       rfl
#check copied
#check source
#print axioms copied
#print axioms source
end NJS_BatchLeaf
