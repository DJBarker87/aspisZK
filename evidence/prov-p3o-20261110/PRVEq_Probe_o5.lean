import Aeneas
import NNH_Tx2SourceConfiguration
import NNH_CorrectConfiguration
import NNH_HostSeed
import PRVEq_AdapterStage1_o1
open Aeneas Aeneas.Std AspisR1
set_option autoImplicit false
noncomputable section
open Lean Elab Command Meta Term in
elab "#hd " t:term : command => runTermElabM fun _ => do
  let e ← Term.elabTerm t none
  let e ← instantiateMVars e
  let r ← whnfD e
  let s := toString (← ppExpr r)
  let s := (s.replace "\n" " ")
  logInfo m!"{t.raw.getArgs.size} {if s.length > 170 then s.take 170 else s}"
section
variable (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op0
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op1
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op2
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op3
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op4
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op5
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op6
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op7
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op8
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op9
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op11
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op16
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op17
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op20
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op21
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op22
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op23
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op24
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op35
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op36
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op37
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op38
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op39
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op40
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op42
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op43
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op44
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op45
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op47
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op48
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op49
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op50
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op51
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op52
#hd (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r).op53
-- current
#hd (DrvC_Installation.currentInstalled (NNH_CorrectConfiguration.configuration NNH_HostSeed.m0 env err r)).op1
#hd (DrvC_Installation.currentInstalled (NNH_CorrectConfiguration.configuration NNH_HostSeed.m0 env err r)).op2
#hd (DrvC_Installation.currentInstalled (NNH_CorrectConfiguration.configuration NNH_HostSeed.m0 env err r)).op3
#hd (DrvC_Installation.currentInstalled (NNH_CorrectConfiguration.configuration NNH_HostSeed.m0 env err r)).op4
#hd (DrvC_Installation.currentInstalled (NNH_CorrectConfiguration.configuration NNH_HostSeed.m0 env err r)).op5
#hd (DrvC_Installation.currentInstalled (NNH_CorrectConfiguration.configuration NNH_HostSeed.m0 env err r)).op6
#hd (DrvC_Installation.currentInstalled (NNH_CorrectConfiguration.configuration NNH_HostSeed.m0 env err r)).op7
#hd (DrvC_Installation.currentInstalled (NNH_CorrectConfiguration.configuration NNH_HostSeed.m0 env err r)).op8
#hd (DrvC_Installation.currentInstalled (NNH_CorrectConfiguration.configuration NNH_HostSeed.m0 env err r)).op9
#hd (DrvC_Installation.currentInstalled (NNH_CorrectConfiguration.configuration NNH_HostSeed.m0 env err r)).op10
#hd (DrvC_Installation.currentInstalled (NNH_CorrectConfiguration.configuration NNH_HostSeed.m0 env err r)).op11
#hd (DrvC_Installation.currentInstalled (NNH_CorrectConfiguration.configuration NNH_HostSeed.m0 env err r)).op12
#hd (DrvC_Installation.currentInstalled (NNH_CorrectConfiguration.configuration NNH_HostSeed.m0 env err r)).op13
#hd (DrvC_Installation.currentInstalled (NNH_CorrectConfiguration.configuration NNH_HostSeed.m0 env err r)).op14
#hd (DrvC_Installation.currentInstalled (NNH_CorrectConfiguration.configuration NNH_HostSeed.m0 env err r)).op15
#hd (DrvC_Installation.currentInstalled (NNH_CorrectConfiguration.configuration NNH_HostSeed.m0 env err r)).op16
#hd (DrvC_Installation.currentInstalled (NNH_CorrectConfiguration.configuration NNH_HostSeed.m0 env err r)).op17
#hd (DrvC_Installation.currentInstalled (NNH_CorrectConfiguration.configuration NNH_HostSeed.m0 env err r)).op18
#hd (DrvC_Installation.currentInstalled (NNH_CorrectConfiguration.configuration NNH_HostSeed.m0 env err r)).op19
#hd (DrvC_Installation.currentInstalled (NNH_CorrectConfiguration.configuration NNH_HostSeed.m0 env err r)).op20
#hd (DrvC_Installation.currentInstalled (NNH_CorrectConfiguration.configuration NNH_HostSeed.m0 env err r)).op21
end
