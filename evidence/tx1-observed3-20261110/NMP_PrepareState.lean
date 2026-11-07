import NMP_EmittedContext
import NMP_EmittedConstants
import NMP_StdMapErr
import NMP_DirectBind
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_PrepareSteps
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted
open NMT_CallTree (Code invoke erase)
abbrev SplitBack := (Slice U8 × Slice U8) → Slice U8
abbrev VecBack := Slice U8 → alloc.vec.Vec U8
/-- Source-order locals retain the actual split/reassembly closures. The two
expansion replies cannot be replaced by slices from independent allocations. -/
inductive State (H W : Type) where
 | allocate (s : Parent H W)
 | split (s : Parent H W) (logical : alloc.vec.Vec U8)
 | semantic (s : Parent H W) (semantic y1 : Slice U8) (back : SplitBack) (vecBack : VecBack)
 | values (s : Parent H W) (semantic y1 : Slice U8) (back : SplitBack) (vecBack : VecBack)
 | view (s : Parent H W) (semantic y1 : Slice U8)
 | observed (s : Parent H W) (v : verifier.View)
 | mark (s : Parent H W) (v : verifier.View) (sem : r1_semantic.Verified H)
 | prepared (s : Parent H W) (v : verifier.View) (sem : r1_semantic.Verified H)

def step {H W : Type} (c : Calls) : State H W → Code (Sum PreparedOut (State H W))
 | .allocate s => do
   let r ← invoke "TX1:064/filled" (14759#usize,0#u8) (c.c1 core.marker.CopyU8 14759#usize 0#u8)
   match r with
   | .Err _ => pure (.inl (.Err verifier.Error.Allocation,s.scratch))
   | .Ok logical => pure (.inr (.split s logical))
 | .split s logical => do
   let (bytes,vecBack) := alloc.vec.Vec.deref_mut logical
   let ((semantic,y1),back) ← invoke "std/split_at_mut" (bytes,13831#usize)
     (core.slice.Slice.split_at_mut bytes 13831#usize)
   pure (.inr (.semantic s semantic y1 back vecBack))
 | .semantic s semantic y1 back vecBack => do
   let src ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
     s.bytes {start:=16#usize,«end»:=7031#usize}
   let (r,after) ← invoke "TX1:098/expand_semantic" (src,semantic) (c.c10 src semantic)
   match r with
   | .Err _ => pure (.inl (.Err verifier.Error.Parse,s.scratch))
   | .Ok _ => pure (.inr (.values s after y1 back vecBack))
 | .values s semantic y1 back vecBack => do
   let src ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
     s.bytes {start:=7031#usize,«end»:=7495#usize}
   let (r,after) ← invoke "TX1:099/expand_values" (src,y1) (c.c11 src y1)
   match r with
   | .Err _ => pure (.inl (.Err verifier.Error.Parse,s.scratch))
   | .Ok _ =>
     let logical := vecBack (back (semantic,after))
     let fullSemantic ← alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
       logical {«end»:=13831#usize}
     let fullY1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
       logical {start:=13831#usize}
     pure (.inr (.view s fullSemantic fullY1))
 | .view s semantic y1 => do
   let r ← invoke "TX1:095/wide_view" (s.bytes,semantic,y1) (c.c2 s.bytes semantic y1)
   match r with
   | .Err e => pure (.inl (.Err e,s.scratch))
   | .Ok v => pure (.inr (.observed s v))
 | .observed s v => do
   let r ← invoke "TX1:137/verify_observed" (s.publicValue,v.semantic,s.hash,s.observer)
     (NMP_prepare.r1_semantic.verify_observed c.c5 c.c6 c.c7 c.c8 c.c9 s.digest s.publicValue v.semantic s.hash s.observer)
   match r with
   | .Err _ => pure (.inl (.Err verifier.Error.Semantic,s.scratch))
   | .Ok sem => pure (.inr (.mark s v sem))
 | .mark s v sem => do
   let _ ← invoke "TX1:191/mark" (s.observer,verifier.Phase.Semantic)
     (c.c4 s.observer verifier.Phase.Semantic)
   pure (.inr (.prepared s v sem))
 | .prepared s v sem => do
   let out ← invoke "TX1:179/Prepared_new" (sem,v,s.hash,s.scratch)
     (c.c3 s.digest sem v s.hash s.scratch)
   pure (.inl out)

def execute {H W : Type} (c : Calls) : Nat → State H W → Code PreparedOut
 | 0,_ => .plain (.fail .panic) .done
 | n+1,s => do
   let r ← step c s
   match r with
   | .inl out => pure out
   | .inr next => execute c n next

def body {H W : Type} (c : Calls) (s : Parent H W) := execute c 8 (.allocate s)
/-- Std map_err receives its existing complete library interpretation. -/
def standard (c : Calls) : Calls := {c with c0:=NMP_StdMapErr.run}
end AspisR1.NMP_PrepareSteps
