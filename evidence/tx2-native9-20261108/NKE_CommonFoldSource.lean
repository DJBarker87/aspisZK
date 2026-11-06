import NKE_RustBind
set_option autoImplicit false
noncomputable section
namespace NKE_CommonFoldSource
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- Source-ordered common spine. Each Rust Result is consumed at its own
occurrence; checked std slices and ownership writeback remain literal. -/
def run (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H) :
 NJU_Log.Run Event (core.result.Result Unit verifier.Error) :=
 NKE_RustBind.bind (NJU_Log.record (.resume ck proof pub)
  (NJJ_Common.resume wr d ck proof pub .S2 hash)) fun (p,a)=>do
 if a.next != NHT_Constants.compact.SPLIT then ok (.Err .Checkpoint) else do
 let g ← NJU_Log.record (.powers p.gamma) (NHT_PacketOps.powers 29#usize p.gamma)
 NHV_ReleaseOps.mark none .CheckpointRead
 let i ← NHT_Constants.compact.OFF_INACTIVE
 let i1 ← NHT_Constants.compact.OFF_ROUND0
 let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  proof {start:=i,«end»:=i1}
 let inactive ← NJU_Log.record (.inactive s) (NJC_ClosedCalls.inactive s)
 NKE_RustBind.bind (liftM (NHT_Constants.core.option.Option.ok_or inactive AdapterRw.aspis_r1_cost_probe.verifier.Error.Parse)) fun inactive=>do
 let i2 ← NHT_Constants.compact.OFF_FOLDED_ROOT
 let i3 ← NHT_Constants.compact.OFF_ROUND1
 let rootBytes ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  proof {start:=i2,«end»:=i3}
 let rootResult ← core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 rootBytes
 let root ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError rootResult
 NKE_RustBind.bind (NJU_Log.record (.merkle proof p root)
  (merkle d proof p root 1#usize hash)) fun _=>do
 NHV_ReleaseOps.mark none (.Merkle NHT_Constants.compact.SPLIT)
 NKE_RustBind.bind (NJU_Log.record (.geometry p.queries a.next)
  (NJC_ClosedCalls.geometry p.queries a.next 22#usize)) fun geometry=>
 NKE_RustBind.bind (NJU_Log.record (.pending a.weights.deref)
  (NJJ_Common.pending rr a.weights.deref)) fun pending=>
 NKE_RustBind.bind (NJU_Log.record (.query proof p a g geometry pending)
  (NJJ_Common.query proof p a g none geometry pending 22#usize)) fun (after,pending)=>do
 let (weights,back) ← lift (alloc.vec.Vec.deref_mut after.weights)
 let output ← NJU_Log.record (.flush pending weights) (Port3_FlushInstall.flush pending weights)
 let weights := back output
 let semantic ← lift (Array.to_slice (Std.Array.empty U8))
 let y1 ← lift (Array.to_slice (Std.Array.empty U8))
 let round0 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  proof {start:=i1,«end»:=i2}
 let i4 ← NHT_Constants.compact.OFF_FINAL
 let round1 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  proof {start:=i3,«end»:=i4}
 let i5 ← NHT_Constants.compact.OFF_OPENINGS
 let finalMessage ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  proof {start:=i4,«end»:=i5}
 let queryBytes ← lift (Array.to_slice (Std.Array.empty U8))
 let view : verifier.View := {
  variant := .S2
  semantic := semantic
  y1 := y1
  inactive := inactive
  round0 := round0
  folded_root := none
  round1 := round1
  final_message := finalMessage
  query_bytes := queryBytes
 }
 let actual : verifier.Accumulator := {after with weights}
 NJU_Log.record (.finish view p actual) (finish view p actual none)

theorem source (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H) :
 NJU_CommonObserved.run wr rr merkle finish d pub proof ck hash none=
 run wr rr merkle finish d pub proof ck hash := by
 simp only [NJU_CommonObserved.run,run,←NKE_RustBind.lower,NJU_Log.prod_cases]
#print axioms source
end NKE_CommonFoldSource
