import NNH_CorrectConfiguration
import NNH_HostEnv
import NNH_RecordedCharge
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNQ_HostDigest
open Aeneas Aeneas.Std Result

def withDigest {F C : Type} (c : DrvC_Installation.Configuration F C)
    (o : AdapterRw.SolanaDigest → Slice (Slice U8) → Result (Array U8 32#usize)) :=
  {c with adapter := {c.adapter with op43 := o}}

theorem split (m0 : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
    (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
    (env env' : RSL.Env) (hp : env.pda = env'.pda) (hc : env.clock = env'.clock)
    (hr : env.reservation = env'.reservation) :
    FIp_Install.configuration err (IDa_Deployed.deployedConfiguration
      (NNH_Tx2Configuration.select (NNH_CorrectConfiguration.residual m0 env) env) err r) r =
    withDigest (FIp_Install.configuration err (IDa_Deployed.deployedConfiguration
      (NNH_Tx2Configuration.select (NNH_CorrectConfiguration.residual m0 env') env') err r) r)
      (fun _ p => LIB_Env.hashv env p) := by
  obtain ⟨s,p,k,v⟩ := env
  obtain ⟨s',p',k',v'⟩ := env'
  dsimp only at hp hc hr
  subst hp hc hr
  rfl
#print axioms split
end AspisR1.NNQ_HostDigest
end
