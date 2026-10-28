import NDO_JGc_TX2_QueryDictionary
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_QueryPowerStep
open Aeneas Aeneas.Std Result AspisR1Stage2
open CheckpointBytes5Output (ofK)

/-- Projection of the actual accumulation return; no line value or output is
supplied independently of the query observation. -/
theorem source (seed : Port3_NativeQueryBody.Ops)
    (proof : Slice U8) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (scratch : Array SAQ_WideABI.E 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (g : verifier.QueryGeometry)
    (b after : verifier.BatchedWeights)
    (cp : Port3_FlushInstall.Canonical a.power)
    (cr : Port3_FlushInstall.Canonical p.rho)
    (run : Port3_NativeQueryBody.verifier.candidate.query_values
      (JGc_TX2_QueryDictionary.ops seed) proof p a scratch obs g b=ok (.Ok (out,after))) :
    ofK out.power=ofK a.power*ofK p.rho ∧
      Port3_FlushInstall.Canonical out.power := by
  obtain ⟨o⟩ := Port4C_QueryValues.observed _ proof p a out scratch obs g b after run
  obtain ⟨product,hprod,hadd,hmul,_⟩ :=
    Port4C_QueryValues.accumulated _ p a out o.node o.value b after o.accumulate
  exact SAQ_Arithmetic.mulK_exact a.power p.rho out.power cp cr hmul
#print axioms source
end AspisR1.JHk_QueryPowerStep
end
