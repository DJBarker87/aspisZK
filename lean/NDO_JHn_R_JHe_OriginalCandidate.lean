import NDO_JHn_R_JHe_ReplaceSuffix
import RPz7_WAdm_ReferenceRun
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_OriginalCandidate
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open Tx1Q_Carriers

theorem source {C H : Type} (base : Ops) (r : Bool) (q : Port3_NativeQueryBody.Ops)
    (g : Port3_NativeGeometryBody.Ops C) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls) (D : aspis_core.digest.Digest32 H) (hash : H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (saved : alloc.vec.Vec U8)
    (owner : WAdm_Domain.SessionAPrepare (WAdm_Execution.actual base r q g B std))
    (ports : Port5Q1_QueryPorts.SessionAPrimitives q)
    (accepted : verifier.candidate.tx1 (WAdm_Execution.actual base r q g B std) D semantic
      pub proof 10#usize hash none=ok (.Ok saved)) :
    verifier.candidate.tx1
      {(WAdm_Execution.actual base r q g B std) with op16:=Tx1Q_Install.writer}
      D semantic pub proof 10#usize hash none=ok (.Ok saved) := by
  let ops := WAdm_Execution.actual base r q g B std
  have slots := WAdm_Execution.actual_slots base r q g B std
  obtain ⟨split,parsed,zero,p,scratch,shape,scan,z,prep,tail⟩ :=
    Tx1Reachability.tx1_success ops D semantic pub proof 10#usize hash saved accepted
  obtain ⟨a,root,geo,b,out,after,flushed,init,batch,geometry,pending,query,flush,write⟩ :=
    Tx1Q_Cuts.suffix ops D pub proof 10#usize hash p scratch saved tail
  have hi := init
  have hb := pending
  have hg := geometry
  have hq := query
  have hf := flush
  have hw := write
  rw [slots.initial] at hi
  rw [slots.pending] at hb
  rw [slots.geometry] at hg
  rw [slots.query] at hq
  rw [slots.flush] at hf
  rw [slots.writer] at hw
  have nq := Tx1Q_Install.query_success (Tx1Q_QueryBridge.leaves q) proof p a out scratch none
    geo b after 10#usize hq
  rw [Tx1Q_QueryBridge.release_leaves] at nq
  let run : WAdm_Execution.Run ops r q g D hash semantic pub proof 10#usize saved := {
    p:=p,zero:=zero,scratch:=scratch,initial:=a,root:=root,geometry:=geo,pending:=b,
    out:=out,after:=after,flushed:=flushed,split_eq:=rfl,prepare_call:=prep,
    initial_call:=Tx1Q_PrefixInstall.initial_success r a hi,batch_call:=batch,
    geometry_call:=Tx1Q_PrefixInstall.geometry_success g p.queries 0#usize 10#usize geo hg,
    pending_call:=Tx1Q_PrefixInstall.pending_success r a.weights.deref b hb,
    query_call:=nq,flush_call:=Tx1Q_Install.flush_success after out.weights.deref flushed hf,
    writer_call:=hw }
  have newWrite : Tx1Q_Install.writer D p {out with weights:=⟨flushed.val,flushed.property⟩}
      proof pub hash=ok saved :=
    (WAdm_ReferenceRun.reference ops r q g D hash semantic pub proof 10#usize saved run owner ports).writer_call
  have newTail := JHe_ReplaceSuffix.source ops (@Tx1Q_Install.writer) D pub proof 10#usize hash
    p scratch a out b after geo flushed saved init geometry pending query flush write newWrite tail
  dsimp only [ops] at shape scan z prep newTail
  have zeroNew : aspis_core.field.wide_exact.WideExact.ZERO
      {(WAdm_Execution.actual base r q g B std) with op16:=Tx1Q_Install.writer}=ok zero := by
    unfold aspis_core.field.wide_exact.WideExact.ZERO at z ⊢
    exact z
  unfold verifier.candidate.tx1
  simp only [compact.SPLIT,show (10#usize !=10#usize)=false from rfl,
    Bool.false_eq_true,if_false,shape,scan,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch,verifier.mark,zeroNew,JHe_ReplaceSuffix.prepare,prep]
  exact newTail
#print axioms source
end AspisR1.JHe_OriginalCandidate
end
