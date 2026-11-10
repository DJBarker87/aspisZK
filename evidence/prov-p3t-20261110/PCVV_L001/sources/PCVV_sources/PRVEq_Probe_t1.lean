import Aeneas
import NNH_HostCtx
import NNH_HostSeed
import NNH_Tx2SourceConfiguration
import NOC_Run5bHost
import PRVEq_AdapterStage2_o1
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
  logInfo m!"{if s.length > 3000 then s.take 3000 else s}"
section
variable {W Tx : Type} (c : AspisR1.NNH_HostCtx.Ctx W Tx)
#hd (AspisR1.NOC_HostCtx.sdk c).op22
#hd (AspisR1.NOC_HostCtx.sdk c).op23
#hd (AspisR1.NOC_HostCtx.sdk c).op20
#hd (AspisR1.NOC_HostCtx.sdk c).op16
#hd (AspisR1.NOC_HostCtx.sdk c).op17
#hd (AspisR1.NOC_HostCtx.sdk c).op11
#hd (AspisR1.NOC_HostCtx.sdk c).op50
#hd (AspisR1.NOC_HostCtx.sdk c).op52
#hd (AspisR1.NOC_HostCtx.sdk c).op49
#hd (AspisR1.NOC_HostCtx.sdk c).op48
#hd (AspisR1.NOC_HostCtx.sdk c).op51
#hd (AspisR1.NOC_HostCtx.sdk c).op45
#hd (AspisR1.NOC_HostCtx.sdk c).op53
#hd (AspisR1.NOC_HostCtx.sdk c).op44
#hd (AspisR1.NOC_HostCtx.sdk c).op21
#hd (AspisR1.NOC_HostCtx.sdk c).op24
#hd (AspisR1.NOC_HostCtx.sdk c).op47
end
