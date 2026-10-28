import NDO_JGy_QueryFrontier
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_WriterContinuation
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry

def afterFlush (p : verifier.Prepared) (out : verifier.Accumulator)
    (flushed : Slice aspis_core.field.QM31) :
    Result (core.result.Result (alloc.vec.Vec U8) verifier.Error) := do
  let saved ← installed.op16 digest p {out with weights:=⟨flushed.val,flushed.property⟩}
    JFx_NativeBytes.proof JFx_NativeBytes.publicInput ()
  verifier.mark none verifier.Phase.CheckpointWrite
  ok (.Ok saved)

/-- The actual query result and actual flushed slice supply op16's accumulator.
No writer success or independently chosen checkpoint is assumed. -/
theorem source (p : verifier.Prepared)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (initial out : verifier.Accumulator) (pending after : verifier.BatchedWeights)
    (g : verifier.QueryGeometry) (flushed : Slice aspis_core.field.QM31)
    (query : installed.op7 JFx_NativeBytes.proof p initial scratch none g pending 10#usize=ok (.Ok (out,after)))
    (flush : installed.op17 after out.weights.deref=ok flushed) :
    JGy_QueryFrontier.afterQuery p scratch initial pending g=afterFlush p out flushed := by
  change installed.op17 after (⟨out.weights.val,out.weights.property⟩ : Slice aspis_core.field.QM31)=ok flushed at flush
  simp (config := {zeta := true,zetaDelta := true,iota := true}) only [JGy_QueryFrontier.afterQuery,query,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
    alloc.vec.Vec.deref_mut,lift,flush,afterFlush,Aeneas.Std.uncurry]
#print axioms source
end AspisR1.JHc_WriterContinuation
end
