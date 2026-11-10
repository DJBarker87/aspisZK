import NOC_Run5bHost
import NNH_Run5bCurrentShape
import NOC_PrepareFront
set_option autoImplicit false
noncomputable section
namespace PCVP_P
open Aeneas Aeneas.Std Result AspisR1
abbrev curN {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :=
  DrvC_Installation.currentInstalled (NOC_HostCtx.configuration c)
-- candidate seed args
theorem a1 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
  curN c = NNH_Run5bCurrentShape.current (NOC_HostCtx.missing c) (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation := rfl
theorem a2 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
  curN c = NNH_Run5bCurrentShape.current (NOC_HostSeed.m0 (NNH_HostCtx.envOf c).reservation) (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation := rfl
theorem a3 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
  curN c = NOC_PrepareFront.cur c := rfl
end PCVP_P
