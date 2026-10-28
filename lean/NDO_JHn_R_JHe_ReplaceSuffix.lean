import NDO_JHn_R_JHe_PrepareWriterFields
import RPz7_Tx1Q_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_ReplaceSuffix
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

theorem prepare (ops : Ops) (w : JHe_WriterCommutation.Writer) {H : Type}
    (D : aspis_core.digest.Digest32 H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (input : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    verifier.candidate.prepare {ops with op16:=w} D semantic proof hash none input=
      verifier.candidate.prepare ops D semantic proof hash none input := by
  unfold verifier.candidate.prepare
  simp only [JHe_PrepareWriterFields.logical,JHe_PrepareWriterFields.semantic,
    JHe_PrepareWriterFields.y1,JHe_PrepareWriterFields.inactive,JHe_PrepareWriterFields.codec]
#print axioms prepare

theorem source (ops : Ops) (w : JHe_WriterCommutation.Writer) {H : Type}
    (D : aspis_core.digest.Digest32 H) (pub proof : Slice U8) (k : Usize) (hash : H)
    (p : verifier.Prepared) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (initial out : verifier.Accumulator) (pending after : verifier.BatchedWeights)
    (g : verifier.QueryGeometry) (flushed : Slice aspis_core.field.QM31) (saved : alloc.vec.Vec U8)
    (init : ops.op20 .S2=ok (.Ok initial))
    (geo : ops.op19 p.queries 0#usize k=ok (.Ok g))
    (pend : ops.op18 initial.weights.deref=ok (.Ok pending))
    (query : ops.op7 proof p initial scratch none g pending k=ok (.Ok (out,after)))
    (flush : ops.op17 after out.weights.deref=ok flushed)
    (old : ops.op16 D p {out with weights:=⟨flushed.val,flushed.property⟩} proof pub hash=ok saved)
    (new : w D p {out with weights:=⟨flushed.val,flushed.property⟩} proof pub hash=ok saved)
    (tail : Tx1Reachability.afterPrepare ops D pub proof k hash none p scratch=ok (.Ok saved)) :
    Tx1Reachability.afterPrepare {ops with op16:=w} D pub proof k hash none p scratch=ok (.Ok saved) := by
  change ops.op17 after (⟨out.weights.val,out.weights.property⟩ : Slice aspis_core.field.QM31)=ok flushed at flush
  simp only [Tx1Reachability.afterPrepare,compact.OFF_FOLDED_ROOT,compact.OFF_ROUND1,init,geo,pend,query,flush,old,new,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,verifier.mark,
    alloc.vec.Vec.deref_mut,lift,Aeneas.Std.uncurry] at tail ⊢
  exact tail
#print axioms source
end AspisR1.JHe_ReplaceSuffix
end
