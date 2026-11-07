import NNG_PrepareEmission087
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Front087
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted NMP_PrepareSteps NMT_CallTree

abbrev FrontOut (H : Type) := core.result.Result (r1_semantic.Verified H × verifier.View) verifier.Error

def observed {H W : Type} (c : Calls) (s : Parent H W) (v : verifier.View) : Code (FrontOut H) := do
 let r ← invoke "TX1:137/verify_observed" (s.publicValue,v.semantic,s.hash,s.observer)
   (NMP_prepare.r1_semantic.verify_observed c.c5 c.c6 c.c7 c.c8 c.c9 s.digest s.publicValue v.semantic s.hash s.observer)
 match r with
 | .Err _=>pure (.Err verifier.Error.Semantic)
 | .Ok sem=>pure (.Ok (sem,v))

def view {H W : Type} (c : Calls) (s : Parent H W) (semantic y1 : Slice U8) : Code (FrontOut H) := do
 let r ← invoke "TX1:095/wide_view" (s.bytes,semantic,y1) (c.c2 s.bytes semantic y1)
 match r with
 | .Err e=>pure (.Err e)
 | .Ok v=>observed c s v

def values {H W : Type} (c : Calls) (s : Parent H W) (semantic y1 : Slice U8)
 (back : SplitBack) (vecBack : VecBack) : Code (FrontOut H) := do
 let src ← (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
   s.bytes {start:=7031#usize,«end»:=7495#usize})
 let (r,after) ← invoke "TX1:099/expand_values" (src,y1) (c.c11 src y1)
 match r with
 | .Err _=>pure (.Err verifier.Error.Parse)
 | .Ok _=>
   let logical := vecBack (back (semantic,after))
   let fullSemantic ← (alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) logical {«end»:=13831#usize})
   let fullY1 ← (alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) logical {start:=13831#usize})
   view c s fullSemantic fullY1

def semantic {H W : Type} (c : Calls) (s : Parent H W) (semantic y1 : Slice U8)
 (back : SplitBack) (vecBack : VecBack) : Code (FrontOut H) := do
 let src ← (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
   s.bytes {start:=16#usize,«end»:=7031#usize})
 let (r,after) ← invoke "TX1:098/expand_semantic" (src,semantic) (c.c10 src semantic)
 match r with
 | .Err _=>pure (.Err verifier.Error.Parse)
 | .Ok _=>values c s after y1 back vecBack

def split {H W : Type} (c : Calls) (s : Parent H W) (logical : alloc.vec.Vec U8) : Code (FrontOut H) := do
 let (bytes,vecBack) := alloc.vec.Vec.deref_mut logical
 let ((semantic,y1),back) ← invoke "std/split_at_mut" (bytes,13831#usize) (core.slice.Slice.split_at_mut bytes 13831#usize)
 NNG_Front087.semantic c s semantic y1 back vecBack

def tree {H W : Type} (c : Calls) (s : Parent H W) : Code (FrontOut H) := do
 let r ← invoke "TX1:064/filled" (14759#usize,0#u8) (c.c1 core.marker.CopyU8 14759#usize 0#u8)
 match r with
 | .Err _=>pure (.Err verifier.Error.Allocation)
 | .Ok logical=>split c s logical
end AspisR1.NNG_Front087
