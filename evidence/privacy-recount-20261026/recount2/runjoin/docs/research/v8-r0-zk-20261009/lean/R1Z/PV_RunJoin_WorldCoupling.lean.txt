import R1Z.PV_RunJoin_Deployed
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_WorldCoupling
open R0Z R0Z.FsAbort R0Z.FsStatement
variable [ProverRwFull.ExternalTypes]
variable {CommitHandle Aux Coins N L B : Type}
variable (runtime : PV_RunJoin_Deployed.Runtime CommitHandle Aux Coins N L B)
variable [Fintype Coins] [Nonempty Coins]

/-- ONE mathematical coupling, on explicit initialized worlds. Native E1
association of the completion map remains separate; it is not obtained from
an arbitrary initialization function or from these two marginal identities. -/
def cp : Coupling (PV_RunJoin_Deployed.rust runtime).RealRand Coins where
  S := PV_RunJoin_Deployed.World runtime
  finS := inferInstance
  nonemptyS := inferInstance
  toR := id
  toM := PV_RunJoin_Deployed.coordinates runtime
  meanR := fun _ => rfl
  meanM := CouplingR1PBin.mp_equiv (PV_RunJoin_Deployed.coordinates runtime)

theorem meanR (f : (PV_RunJoin_Deployed.rust runtime).RealRand → ℚ) :
    mean (fun s => f ((cp runtime).toR s)) = mean f := (cp runtime).meanR f

theorem meanM (f : Coins → ℚ) :
    mean (fun s => f ((cp runtime).toM s)) = mean f := (cp runtime).meanM f

#print axioms cp
#print axioms meanR
#print axioms meanM
end R1Z.PV_RunJoin_WorldCoupling
