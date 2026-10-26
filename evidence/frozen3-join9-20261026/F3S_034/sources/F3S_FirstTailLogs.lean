import F3S_FirstTailCode
import F3S_Forward
import GExq_FirstErasure
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_FirstTailLogs
open Aeneas Aeneas.Std Result CheckpointBytes5Effect AspisR1CurrentCaller
local instance : MonadLift Result Code where monadLift := CheckpointBytes5Effect.liftResult
attribute [local irreducible] GExq_BatchSource.current GExp_FirstCode.writerCode
 theorem on_calls {Hash : Type} (base : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (D : aspis_core.digest.Digest32 Hash)
    (publicBytes proof : Slice U8) (k : Usize) (hash : Hash) (p : verifier.Prepared)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (a out : verifier.Accumulator) (geo : verifier.QueryGeometry) (pending after : verifier.BatchedWeights)
    (flushed : Slice aspis_core.field.QM31) (root : Array U8 32#usize) (view : Slice U8)
    (initial : (GExp_FirstCode.installed base B std).op20 .S2=ok (.Ok a))
    (start : compact.OFF_FOLDED_ROOT (GExp_FirstCode.installed base B std)=ok 7751#usize)
    (finish : compact.OFF_ROUND1 (GExp_FirstCode.installed base B std)=ok 7783#usize)
    (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start:=7751#usize,«end»:=7783#usize}=ok view)
    (copy : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view=ok (.Ok root))
    (batch : erase (SdkC_Source.dictionary hashv) () (GExq_BatchSource.current D hash proof p root)=ok (.Ok ()))
    (geometry : (GExp_FirstCode.installed base B std).op19 p.queries 0#usize k=ok (.Ok geo))
    (newPending : (GExp_FirstCode.installed base B std).op18 a.weights.deref=ok (.Ok pending))
    (query : (GExp_FirstCode.installed base B std).op7 proof p a scratch none geo pending k=ok (.Ok (out,after)))
    (flush : (GExp_FirstCode.installed base B std).op17 after out.weights.deref=ok flushed) :
    SdkC_Source.readLog (SdkC_Source.run hashv
      (F3S_FirstTailCode.code base B std D hash publicBytes proof k p scratch) []).2=
      SdkC_Source.readLog (SdkC_Source.run hashv (GExq_BatchSource.current D hash proof p root) []).2 ++
      SdkC_Source.readLog (SdkC_Source.run hashv (GExp_FirstCode.writerCode p
        {out with weights:=⟨flushed.val,flushed.property⟩} proof publicBytes) []).2 := by
  simp only [F3S_FirstTailCode.code,initial,start,finish,range,copy,
    liftM,MonadLift.monadLift,MonadLiftT.monadLift,
    Bind.bind,F3S_Forward.lift_ok,core.result.Result.Insts.CoreOpsTry.branch,
    verifier.mark,core.result.Result.unwrap,geometry,newPending,query,flush]
  trace_state

#print axioms on_calls
end AspisR1.F3S_FirstTailLogs
end
