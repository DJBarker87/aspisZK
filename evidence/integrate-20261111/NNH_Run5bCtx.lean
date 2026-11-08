import NNR_Retime
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bCtx
open Aeneas Aeneas.Std Result
abbrev Fixed := NNH_HostCtx.Fixed
abbrev World := NNH_HostCtx.World
abbrev Ctx := NNH_HostCtx.Ctx
abbrev envOf {W Tx : Type} (c : Ctx W Tx) := NFB_NMFBHost.env2 c
abbrev missingLit := @NNH_HostCtx.missingLit
abbrev missing := @NNH_HostCtx.missing
abbrev Exhibited := @NNH_HostCtx.Exhibited
abbrev base := @NNH_HostCtx.base
abbrev configuration := @NNH_HostCtx.configuration
abbrev sdk := @NNH_HostCtx.sdk
abbrev model1 := @NNH_HostCtx.model1
abbrev model2 := @NNH_HostCtx.model2
abbrev hashv := @NNH_HostCtx.hashv
abbrev exhibited := @NNH_HostCtx.exhibited
abbrev extraction := @NNH_HostCtx.extraction

theorem missing_at_slot {W Tx : Type} (c : Ctx W Tx) :
 NNH_Tx2Configuration.select (NNH_CorrectConfiguration.residual NNH_HostSeed.m0 (envOf c))
 (envOf c) = missingLit c := NNR_Retime.missing c

theorem env_unique {W Tx : Type} (c : Ctx W Tx) (env : RSL.Env)
 (h : NNH_HostEnv.EnvRep (DGP_HostDigest.shaReply c.sha256) c.fixed.pda
  (NND_Carrier.reply NND_Carrier.slot c.j.slot) c.fixed.reservation env) : env = envOf c :=
 NNH_PreflightEnv.unique _ _ _ _ env h

theorem selected_clock {W Tx : Type} (c : Ctx W Tx) :
 NNH_HostWeak241.clock (envOf c) = c.j.slot := NNR_Clock.M1a c
#print axioms missing_at_slot
#print axioms env_unique
#print axioms selected_clock
#print axioms extraction
end AspisR1.NNH_Run5bCtx
end
