import NLJ_PrepareState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code)
def step {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let o := ops i
 match s.locals with
 | .allocate =>
   let n ← compact.LOGICAL_SEMANTIC o
   let ny ← compact.LOGICAL_Y1
   let total ← n + ny
   let r ← o.op1 core.marker.CopyU8 total 0#u8
   match r with
   | .Err _ => pure (.inl (.Err verifier.Error.Allocation,i.scratch))
   | .Ok logical => pure (.inr (advance s (.split n logical)))
 | .split n logical =>
   let (bytes,vecBack) ← lift (alloc.vec.Vec.deref_mut logical)
   let ((semantic,y1),splitBack) ← core.slice.Slice.split_at_mut bytes n
   pure (.inr (advance s (.semanticRange n semantic y1 splitBack vecBack)))
 | .semanticRange n semantic y1 splitBack vecBack =>
   let off ← compact.OFF_SEMANTIC o
   let offY1 ← compact.OFF_Y1 o
   let compressed ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) i.proof {start:=off,«end»:=offY1}
   pure (.inr (advance s (.expandSemantic n offY1 semantic y1 compressed splitBack vecBack)))
 | .expandSemantic n offY1 semantic y1 compressed splitBack vecBack =>
   let (r,semanticAfter) ← o.op10 compressed semantic
   match r with
   | .Ok _ => pure (.inr (advance s (.valueRange n offY1 semanticAfter y1 splitBack vecBack)))
   | .Err e =>
     let r ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual verifier.Prepared (verifier.Error.Insts.CoreConvertFromCodecError o) (.Err e)
     pure (.inl (r,i.scratch))
 | .valueRange n offY1 semantic y1 splitBack vecBack =>
   let offInactive ← compact.OFF_INACTIVE o
   let compressed ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) i.proof {start:=offY1,«end»:=offInactive}
   pure (.inr (advance s (.expandValues n semantic y1 compressed splitBack vecBack)))
 | .expandValues n semantic y1 compressed splitBack vecBack =>
   let (r,y1After) ← o.op11 compressed y1
   match r with
   | .Ok _ => pure (.inr (advance s (.rebuild n semantic y1After splitBack vecBack)))
   | .Err e =>
     let r ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual verifier.Prepared (verifier.Error.Insts.CoreConvertFromCodecError o) (.Err e)
     pure (.inl (r,i.scratch))
 | .rebuild n semantic y1 splitBack vecBack =>
   let logical := vecBack (splitBack (semantic,y1))
   let semanticFull ← alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) logical {«end»:=n}
   let y1Full ← alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) logical {start:=n}
   pure (.inr (advance s (.view logical semanticFull y1Full)))
 | .view logical semantic y1 =>
   let r ← o.op5 i.proof semantic y1
   match r with
   | .Err e => pure (.inl (.Err e,i.scratch))
   | .Ok v => pure (.inr (advance s (.semantic logical v)))
 | .semantic logical v =>
   let r ← S1SemanticCodeInstallation.code AspisS1ExtractedRoundChildren.children
    (ClaimsUnrolledFinish.install i.std i.boundaries) i.digest i.publicValue v.semantic i.hash
   pure (.inr (advance s (.mapSemantic logical v r)))
 | .mapSemantic logical v r =>
   match r with
   | .Err _ => pure (.inl (.Err verifier.Error.Semantic,i.scratch))
   | .Ok sem => pure (.inr (advance s (.mark logical v sem)))
 | .mark logical v sem =>
   verifier.mark none verifier.Phase.Semantic
   pure (.inr (advance s (.constructor logical v sem)))
 | .constructor _ v sem =>
   let out ← BorrowedClaimPrepared.closedPreparationCode i.digest sem v i.hash i.scratch
   pure (.inl out)
end AspisR1.NLJ_Prepare
end
