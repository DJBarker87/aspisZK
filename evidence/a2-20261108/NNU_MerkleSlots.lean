import NNH_Tx2OpenSlots
import NLL_Tx2Caller
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_MerkleSlots
open Aeneas Aeneas.Std Result VTop_Stages

theorem installed (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 {X : Type} (D : aspis_core.digest.Digest32 X) (proof : Slice U8) (p : verifier.Prepared)
 (root : Array U8 32#usize) (batch : Usize) (hash : X) :
 (NNH_Tx2SlotTransport.stage m env err r).op5 D proof p root batch hash =
 Port4B_Install.batch D proof p root batch hash := by
 change Op5T_Install.stageBatch Port4B_Install.leaves D proof p root batch hash = _
 exact Op5T_Concrete.stage_source D proof p root batch hash

theorem same_resume (env : RSL.Env) (pub proof ck : Slice U8)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (resume : NJJ_Common.resume (LIBB_Tx2Reservation.reservation env) (LIBB_PartitionEnv.digest env)
  ck proof pub .S2 ()=.ok (.Ok (p,a))) :
 ∀ j,j<22 → p.queries.val[j]!.val<262144 :=
 NLL_Tx2Caller.resumed _ _ ck proof pub () p a resume
#print axioms installed
#print axioms same_resume
end AspisR1.NNU_MerkleSlots
end
