import NJK_COMBINED_IMPORT
set_option pp.all true
#print AdapterRw.observer
#print AspisR1.NP6_StdModel.Reservation
#print NIG_FilledCoverage.source
#print NHM_Filled64.cohort
#print NIG_FinishInput.Domain
#print AspisR1.NIW_AlignFinishPort.Cut
#print AspisR1.NIW_AlignFinishPairCertificate.Bound
#print AspisR1.NJF_Root.finish
#print AspisR1.NIX_SamplerLaw.adopted
#print AspisR1.NIX_Cuts.sampler_replies
#print AspisR1.NIX_ResidualCut.packet
#print AspisR1.NIX_ValidatedCut.source
#print AspisR1.NIX_DispatchRun.returned
#print axioms AspisR1.NJH_Observer.emitted
#print axioms AspisR1.NJF_Root.finish
#print axioms AspisR1.NIX_SamplerLaw.adopted
#print axioms AspisR1.NIX_ResidualCut.packet
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? `AdapterRw.observer | throwError "observer owner missing"
  logInfo m!"NJK_OBSERVER_OWNER {env.header.moduleNames[idx]!}"
