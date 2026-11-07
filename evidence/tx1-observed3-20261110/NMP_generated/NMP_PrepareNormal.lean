import NMP_PrepareState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_PrepareSuffix
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted NMP_PrepareSteps

def f7 {H W : Type} (c : Calls) (s : Parent H W) (v : verifier.View) (sem : r1_semantic.Verified H) :=
 c.c3 s.digest sem v s.hash s.scratch

def f6 {H W : Type} (c : Calls) (s : Parent H W) (v : verifier.View) (sem : r1_semantic.Verified H) : Result PreparedOut := do
 c.c4 s.observer verifier.Phase.Semantic
 f7 c s v sem

def f5 {H W : Type} (c : Calls) (s : Parent H W) (v : verifier.View) : Result PreparedOut := do
 let r ← NMP_prepare.r1_semantic.verify_observed c.c5 c.c6 c.c7 c.c8 c.c9 s.digest s.publicValue v.semantic s.hash s.observer
 match r with
 | .Err _ => .ok (.Err verifier.Error.Semantic,s.scratch)
 | .Ok sem => f6 c s v sem

def f4 {H W : Type} (c : Calls) (s : Parent H W) (semantic y1 : Slice U8) : Result PreparedOut := do
 let r ← c.c2 s.bytes semantic y1
 match r with
 | .Err e => .ok (.Err e,s.scratch)
 | .Ok v => f5 c s v

def f3 {H W : Type} (c : Calls) (s : Parent H W) (semantic y1 : Slice U8)
 (back : SplitBack) (vecBack : VecBack) : Result PreparedOut := do
 let src ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
   s.bytes {start:=7031#usize,«end»:=7495#usize}
 let (r,after) ← c.c11 src y1
 match r with
 | .Err _ => .ok (.Err verifier.Error.Parse,s.scratch)
 | .Ok _ =>
   let logical := vecBack (back (semantic,after))
   let fullSemantic ← alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
     logical {«end»:=13831#usize}
   let fullY1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
     logical {start:=13831#usize}
   f4 c s fullSemantic fullY1

def f2 {H W : Type} (c : Calls) (s : Parent H W) (semantic y1 : Slice U8)
 (back : SplitBack) (vecBack : VecBack) : Result PreparedOut := do
 let src ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
   s.bytes {start:=16#usize,«end»:=7031#usize}
 let (r,after) ← c.c10 src semantic
 match r with
 | .Err _ => .ok (.Err verifier.Error.Parse,s.scratch)
 | .Ok _ => f3 c s after y1 back vecBack

def f1 {H W : Type} (c : Calls) (s : Parent H W) (logical : alloc.vec.Vec U8) : Result PreparedOut := do
 let (bytes,vecBack) := alloc.vec.Vec.deref_mut logical
 let ((semantic,y1),back) ← core.slice.Slice.split_at_mut bytes 13831#usize
 f2 c s semantic y1 back vecBack

def f0 {H W : Type} (c : Calls) (s : Parent H W) : Result PreparedOut := do
 let r ← c.c1 core.marker.CopyU8 14759#usize 0#u8
 match r with
 | .Err _ => .ok (.Err verifier.Error.Allocation,s.scratch)
 | .Ok logical => f1 c s logical
end AspisR1.NMP_PrepareSuffix
