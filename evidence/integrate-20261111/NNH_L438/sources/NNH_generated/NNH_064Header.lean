import NNH_064WeakField
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_064Header
open Aeneas Aeneas.Std NNH_Libraries NNH_064Install NNH_064WeakField

def header (env : RSL.Env) (pub pr ck : RSL.Bytes) : Prop :=
 NLW_ReaderHeader.decode (NNC_ByteCarriers.protocol ck)=
 some (LIBB_PartitionEnv.H env (NNC_ByteCarriers.protocol pr),
       LIBB_PartitionEnv.H env (NNC_ByteCarriers.protocol pub))

/-- Header at the same Env backend. The external hash realization belongs
to literal-host wiring; it is not added to Dom064 or hidden in w. -/
theorem okHeader (pub pr ck : RSL.Bytes) (env : RSL.Env)
 (o : RSL.Obs (Except V0.VErr Unit))
 (domain : RSL.TX2_241.Dom064 (RSL.TAS.lib V0 (fun _ _=>True) w) (pub,pr,ck))
 (source : w pub pr ck env o) (ok : o.exit=.ret (.ok ()))
 (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest (LIBB_PartitionEnv.digest env)) ()
  (LIBB_PartitionEnv.H env)) : header env pub pr ck :=
 NNC_ObservedLaw.accepted_header (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) ()
  frame pub pr ck domain.1 domain.2.1 domain.2.2.1 oracle env o source ok
#print axioms okHeader
end AspisR1.NNH_064Header
