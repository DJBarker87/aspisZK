import RPx_Deployed
import RPz7_SdkD_Tx1Suffix
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCL_DriverCuts
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
attribute [local irreducible] verifier.candidate.tx1 verifier.candidate.prepare
  Tx1Reachability.afterPrepare

/-- Cuts of ONE accepted emitted TX1 body. The proof, public bytes, hash,
returned checkpoint and all intermediate carriers stay indexed by that call.
This is a model inversion, not a native Rust association. -/
structure Cuts (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (hash : H) (saved : alloc.vec.Vec U8) where
  parsed : transport.Variant
  zero : aspis_core.field.wide_exact.WideExact
  prepared : verifier.Prepared
  scratch : Array aspis_core.field.wide_exact.WideExact 29#usize
  initial : verifier.Accumulator
  root : Array U8 32#usize
  geometry : verifier.QueryGeometry
  pending : verifier.BatchedWeights
  out : verifier.Accumulator
  after : verifier.BatchedWeights
  flushed : Slice aspis_core.field.QM31
  rootView : Slice U8
  shape : ops.op3 proof = ok (.Ok parsed)
  scan : ops.op4 proof = ok (.Ok ())
  zero_call : aspis_core.field.wide_exact.WideExact.ZERO ops = ok zero
  prepare : verifier.candidate.prepare ops D semantic proof hash none
    (Array.repeat 29#usize zero) = ok (.Ok prepared,scratch)
  root_range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    proof {start:=7751#usize,«end»:=7783#usize} = ok rootView
  root_copy : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 rootView = ok (.Ok root)
  initial_call : ops.op20 .S2 = ok (.Ok initial)
  batch : ops.op6 D proof prepared root 0#usize hash = ok (.Ok ())
  geometry_call : ops.op19 prepared.queries 0#usize 10#usize = ok (.Ok geometry)
  pending_call : ops.op18 initial.weights.deref = ok (.Ok pending)
  query : ops.op7 proof prepared initial scratch none geometry pending 10#usize = ok (.Ok (out,after))
  flush : ops.op17 after out.weights.deref = ok flushed
  checkpoint : ops.op16 D prepared {out with weights := ⟨flushed.val,flushed.property⟩}
    proof pub hash = ok saved

/-- The cuts are derived, never assumed as another accepted execution. -/
theorem accepted (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (hash : H) (saved : alloc.vec.Vec U8)
    (start : compact.OFF_FOLDED_ROOT ops = ok 7751#usize)
    (finish : compact.OFF_ROUND1 ops = ok 7783#usize)
    (returned : verifier.candidate.tx1 ops D semantic pub proof split hash none = ok (.Ok saved)) :
    split = 10#usize ∧ Nonempty (Cuts ops D semantic pub proof hash saved) := by
  obtain ⟨hs,parsed,zero,p,scratch,hshape,hscan,hzero,hprep,tail⟩ :=
    Tx1Reachability.tx1_success ops D semantic pub proof split hash saved returned
  have same : split = 10#usize := by simpa only [compact.SPLIT] using hs
  cases same
  obtain ⟨a,root,geo,b,out,after,flushed,view,range,copy,init,batch,geometry,pending,query,flush,write⟩ :=
    SdkD_Tx1Suffix.suffix ops D pub proof 10#usize hash p scratch saved start finish tail
  exact ⟨rfl,⟨⟨parsed,zero,p,scratch,a,root,geo,b,out,after,flushed,view,
    hshape,hscan,hzero,hprep,range,copy,init,batch,geometry,pending,query,flush,write⟩⟩⟩
#print axioms accepted
end AspisR1.NCL_DriverCuts
end
