import NDO_JHk_CurrentRhsFormula
import JHk_KUnique
import NDO_JHc_QueryPost
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_EUnique
open Aeneas Aeneas.Std
theorem source (x y : SAQ_WideABI.E)
    (hx : Port4C_QueryArithmetic.CanonE x) (hy : Port4C_QueryArithmetic.CanonE y)
    (same : CheckpointBytes5Output.ofE x=CheckpointBytes5Output.ofE y) : x=y := by
  rcases x with ⟨a,b⟩
  rcases y with ⟨c,d⟩
  have h0 := JHk_KUnique.source a c hx.1 hy.1 (congrArg (fun z => z.re) same)
  have h1 := JHk_KUnique.source b d hx.2 hy.2 (congrArg (fun z => z.im) same)
  cases h0
  cases h1
  rfl
#print axioms source
end AspisR1.JHk_EUnique
namespace AspisR1.JHk_QueryRhs
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry
theorem source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (initial out : verifier.Accumulator) (pending after : verifier.BatchedWeights)
    (g : verifier.QueryGeometry)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch))
    (queries : p.queries=JFq_Queries.value)
    (init : installed.op20 .S2=ok (.Ok initial))
    (pend : installed.op18 initial.weights.deref=ok (.Ok pending))
    (geo : installed.op19 p.queries 0#usize 10#usize=ok (.Ok g))
    (query : installed.op7 JFx_NativeBytes.proof p initial scratch none g pending 10#usize=
      ok (.Ok (out,after))) :
    Tx1Q_Carriers.e out.rhs=JFq_Rhs.scalar := by
  have meaning := JHk_CurrentRhsFormula.source p input scratch initial out pending after g
    prepare queries init pend geo query
  obtain ⟨out1,after1,flushed,run,flush,next,length,variant,canon,cp⟩ :=
    JHc_QueryPost.source p input scratch initial pending g prepare queries init pend geo
  have same := congrArg Prod.fst (core.result.Result.Ok.inj (Result.ok.inj (run.symm.trans query)))
  change out1=out at same
  rw [same] at canon
  exact JHk_EUnique.source _ _ canon JFn_AccumulatorCanonical.rhs meaning
#print axioms source
end AspisR1.JHk_QueryRhs
end
