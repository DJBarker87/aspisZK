import NDO_JHk_LineValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_QueryRhsStep
open Aeneas Aeneas.Std Result AspisR1Stage2
open CheckpointBytes5Output (ofE ofK)

theorem backend (seed : Port3_NativeQueryBody.Ops) :
    Port4C_QueryArithmetic.SessionABackends (JGc_TX2_QueryDictionary.ops seed) :=
  ⟨SAQ_MixedSource.mulE_exact,SAQ_Arithmetic.add_exact,SAQ_Arithmetic.mulK_exact⟩
#print axioms backend

/-- The actual query's rhs contribution, including the SAME recovered line
operand. No independently chosen folded output is supplied. -/
theorem source (i : Fin 10) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (b after : verifier.BatchedWeights)
    (alpha : p.alpha=JFo_Prepared.value.alpha)
    (next : a.next=JGw_GeometryReads.cursor i)
    (cp : Port3_FlushInstall.Canonical a.power)
    (crho : Port3_FlushInstall.Canonical p.rho)
    (crhs : Port4C_QueryArithmetic.CanonE a.rhs)
    (run : Port3_NativeQueryBody.verifier.candidate.query_values JHa_AllQueries.ops
      JFx_NativeBytes.proof p a JFr_TX2_Powers.value none
      (JGp_Geometry.value () JGp_Seeds.geometry) b=ok (.Ok (out,after))) :
    ofE out.rhs=ofE a.rhs+LiteralOpeningView.eK (ofK a.power)*JHk_LineValues.value i := by
  obtain ⟨o,same,canon⟩ := JHk_LineRead.source i p a out b after alpha next run
  have h := (Port4C_QueryArithmetic.accumulation JHa_AllQueries.ops (backend JGp_Seeds.query)
    p a out o.node o.value b after cp crho crhs canon o.accumulate).1
  rw [same,JHk_LineValues.source] at h
  exact h
#print axioms source
end AspisR1.JHk_QueryRhsStep
end
