import NDO_JGr_Geometry
import NDO_JGp_FoldedRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_QueryFrontier
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry
attribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.proofBytes JFw_Frames.window

/-- Verbatim remainder beginning at the actual query call; no successful
query, flush, writer result or separately chosen saved vector is assumed. -/
def afterQuery (p : verifier.Prepared)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (initial : verifier.Accumulator) (pending : verifier.BatchedWeights) (g : verifier.QueryGeometry) :
    Result (core.result.Result (alloc.vec.Vec U8) verifier.Error) := do
  let r8 ← installed.op7 JFx_NativeBytes.proof p initial scratch none g pending 10#usize
  let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r8
  match cf7 with
  | .Continue val4 =>
    let (a, pending) := val4
    let (s2, back) ← lift (alloc.vec.Vec.deref_mut a.weights)
    let s3 ← installed.op17 pending s2
    let v := back s3
    let bytes ← installed.op16 digest p {a with weights:=v}
      JFx_NativeBytes.proof JFx_NativeBytes.publicInput ()
    verifier.mark none verifier.Phase.CheckpointWrite
    ok (.Ok bytes)
  | .Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec U8) (core.convert.FromSame verifier.Error) residual

theorem folded_offset : compact.OFF_FOLDED_ROOT installed=ok 7751#usize := by
  unfold compact.OFF_FOLDED_ROOT
  have offset : installed.op21=ok 7527#usize := rfl
  rw [offset,bind_tc_ok]
  apply UsizeArithmetic.add_eq_ok <;> scalar_tac
#print axioms folded_offset

theorem round_offset : compact.OFF_ROUND1 installed=ok 7783#usize := by
  unfold compact.OFF_ROUND1
  rw [folded_offset,bind_tc_ok]
  apply UsizeArithmetic.add_eq_ok <;> scalar_tac
#print axioms round_offset

theorem source (p : verifier.Prepared)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (initial : verifier.Accumulator) (pending : verifier.BatchedWeights) (g : verifier.QueryGeometry)
    (init : installed.op20 .S2=ok (.Ok initial))
    (batch : installed.op6 digest JFx_NativeBytes.proof p JGe_View.folded 0#usize ()=ok (.Ok ()))
    (geo : installed.op19 p.queries 0#usize 10#usize=ok (.Ok g))
    (pend : installed.op18 initial.weights.deref=ok (.Ok pending)) :
    Tx1Reachability.afterPrepare installed digest JFx_NativeBytes.publicInput JFx_NativeBytes.proof
      10#usize () none p scratch=afterQuery p scratch initial pending g := by
  unfold Tx1Reachability.afterPrepare
  simp only [init,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,verifier.mark,
    folded_offset,round_offset,JGp_FoldedRead.range,JGp_FoldedRead.copy,
    core.result.Result.unwrap,batch,geo,pend]
  rfl
#print axioms source
end AspisR1.JGy_QueryFrontier
end
