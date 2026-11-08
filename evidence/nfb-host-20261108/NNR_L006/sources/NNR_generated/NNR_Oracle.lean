import NFB_NMFBHost
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNR_Oracle
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge

theorem M2e : NFB_NMFBHost.M2e := by
 intro H pda k r parts digest returned
 change LIB_Env.hashv (DGP_HostDigest.envInst H pda k r) parts = .ok digest at returned
 rw [DGP_HostDigest.op43_value] at returned
 cases returned
 exact state_roundtrip _
#print axioms M2e
end AspisR1.NNR_Oracle
end
