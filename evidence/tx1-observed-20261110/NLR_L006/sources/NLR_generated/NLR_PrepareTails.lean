import NLJ_PrepareGoal
import NLJ_Monad
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_PrepareTails
open Aeneas Aeneas.Std Result AspisR1CurrentCaller AspisR1PublicPreparation
open PreparedHashCode (Code run)
open NLJ_Prepare
def tail_constructor (cfg : Configuration) {H : Type} (i : Input H) (logical : alloc.vec.Vec U8) (v : verifier.View) (sem : r1_semantic.Verified H) : Code Out := do
 let o := ops cfg
 let out ← BorrowedClaimPrepared.closedPreparationCode i.digest sem v i.hash i.scratch
 pure out

def tail_mark (cfg : Configuration) {H : Type} (i : Input H) (logical : alloc.vec.Vec U8) (v : verifier.View) (sem : r1_semantic.Verified H) : Code Out := do
 let o := ops cfg
 verifier.mark none verifier.Phase.Semantic
 tail_constructor cfg i logical v sem

def tail_mapSemantic (cfg : Configuration) {H : Type} (i : Input H) (logical : alloc.vec.Vec U8) (v : verifier.View) (r : core.result.Result (r1_semantic.Verified H) r1_wire.Error) : Code Out := do
 let o := ops cfg
 match r with
 | .Err _ => pure (.Err verifier.Error.Semantic,i.scratch)
 | .Ok sem => tail_mark cfg i logical v sem

def tail_semantic (cfg : Configuration) {H : Type} (i : Input H) (logical : alloc.vec.Vec U8) (v : verifier.View) : Code Out := do
 let o := ops cfg
 let r ← S1SemanticCodeInstallation.code AspisS1ExtractedRoundChildren.children
  (ClaimsUnrolledFinish.install cfg.std cfg.boundaries) i.digest i.publicValue v.semantic i.hash
 tail_mapSemantic cfg i logical v r

def tail_view (cfg : Configuration) {H : Type} (i : Input H) (logical : alloc.vec.Vec U8) (semantic y1 : Slice U8) : Code Out := do
 let o := ops cfg
 let r ← o.op5 i.proof semantic y1
 match r with
 | .Err e => pure (.Err e,i.scratch)
 | .Ok v => tail_semantic cfg i logical v

def tail_rebuild (cfg : Configuration) {H : Type} (i : Input H) (n : Usize) (semantic y1 : Slice U8) (splitBack : SplitBack) (vecBack : VecBack) : Code Out := do
 let o := ops cfg
 let logical := vecBack (splitBack (semantic,y1))
 let semanticFull ← alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) logical {«end»:=n}
 let y1Full ← alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) logical {start:=n}
 tail_view cfg i logical semanticFull y1Full

def tail_expandValues (cfg : Configuration) {H : Type} (i : Input H) (n : Usize) (semantic y1 compressed : Slice U8) (splitBack : SplitBack) (vecBack : VecBack) : Code Out := do
 let o := ops cfg
 let (r,y1After) ← o.op11 compressed y1
 match r with
 | .Ok _ => tail_rebuild cfg i n semantic y1After splitBack vecBack
 | .Err e =>
   let r ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual verifier.Prepared (verifier.Error.Insts.CoreConvertFromCodecError o) (.Err e)
   pure (r,i.scratch)

def tail_valueRange (cfg : Configuration) {H : Type} (i : Input H) (n offY1 : Usize) (semantic y1 : Slice U8) (splitBack : SplitBack) (vecBack : VecBack) : Code Out := do
 let o := ops cfg
 let offInactive ← compact.OFF_INACTIVE o
 let compressed ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) i.proof {start:=offY1,«end»:=offInactive}
 tail_expandValues cfg i n semantic y1 compressed splitBack vecBack

def tail_expandSemantic (cfg : Configuration) {H : Type} (i : Input H) (n offY1 : Usize) (semantic y1 compressed : Slice U8) (splitBack : SplitBack) (vecBack : VecBack) : Code Out := do
 let o := ops cfg
 let (r,semanticAfter) ← o.op10 compressed semantic
 match r with
 | .Ok _ => tail_valueRange cfg i n offY1 semanticAfter y1 splitBack vecBack
 | .Err e =>
   let r ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual verifier.Prepared (verifier.Error.Insts.CoreConvertFromCodecError o) (.Err e)
   pure (r,i.scratch)

def tail_semanticRange (cfg : Configuration) {H : Type} (i : Input H) (n : Usize) (semantic y1 : Slice U8) (splitBack : SplitBack) (vecBack : VecBack) : Code Out := do
 let o := ops cfg
 let off ← compact.OFF_SEMANTIC o
 let offY1 ← compact.OFF_Y1 o
 let compressed ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) i.proof {start:=off,«end»:=offY1}
 tail_expandSemantic cfg i n offY1 semantic y1 compressed splitBack vecBack

def tail_split (cfg : Configuration) {H : Type} (i : Input H) (n : Usize) (logical : alloc.vec.Vec U8) : Code Out := do
 let o := ops cfg
 let (bytes,vecBack) ← lift (alloc.vec.Vec.deref_mut logical)
 let ((semantic,y1),splitBack) ← core.slice.Slice.split_at_mut bytes n
 tail_semanticRange cfg i n semantic y1 splitBack vecBack

def tail_allocate (cfg : Configuration) {H : Type} (i : Input H)  : Code Out := do
 let o := ops cfg
 let n ← compact.LOGICAL_SEMANTIC o
 let ny ← compact.LOGICAL_Y1
 let total ← n + ny
 let r ← o.op1 core.marker.CopyU8 total 0#u8
 match r with
 | .Err _ => pure (.Err verifier.Error.Allocation,i.scratch)
 | .Ok logical => tail_split cfg i n logical

end AspisR1.NLR_PrepareTails
end
