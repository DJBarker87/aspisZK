import NLM_DeployedOps
import NLQ_Stage1Body
import NLD_Stage1Source
set_option autoImplicit false
noncomputable section
namespace NLQ_InstalledStage1
open Aeneas Aeneas.Std Result AspisR1 AspisR1.IDa_Deployed
/-- Exact headline-selected SDK dictionary, rather than a free Ops parameter.
This is organization only: missing still contains adapter/current/stage Ops;
no slot law or native interpretation is discharged by this specialization. -/
theorem owned {CoreError : Type} (missing : Uninstalled CoreError) (indexError : CoreError)
 (reservation : NP6_StdModel.Reservation) (p : AdapterRw.solana_pubkey.Pubkey)
 (a : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount) (d : Slice U8) :
 (NLD_Stage1Source.stage1Owned (NLM_DeployedOps.ops missing indexError reservation) p a d).2=
 AdapterRw.r1_pool_adapter.owned.stage1_owned (NLM_DeployedOps.ops missing indexError reservation) p a d :=
 NLD_Stage1Source.erasure _ p a d
/-- Complete returning-allocation source branch. Child Err, fail and div are
split INSIDE the suffix theorem, and the copy extent is derived there. The
allocator branch is local support, not an admitted root success hypothesis. -/
theorem stage1 {CoreError : Type} (missing : Uninstalled CoreError) (indexError : CoreError)
 (reservation : NP6_StdModel.Reservation) (e : S2W_D189Entry.Entry)
 (p : AdapterRw.solana_pubkey.Pubkey) (d : Slice U8) (tx1 : NLQ_Route.Tx1 d) :
 (NLQ_Stage1Parent.G e (NLM_DeployedOps.ops missing indexError reservation) p d 3
   (.ok ()) (.ok ()) (.ok ())).result=
 (do let child ← AdapterRw.r1_pool_adapter.owned.stage1_owned
      (NLM_DeployedOps.ops missing indexError reservation) p e.first d
     match child with
     | .Ok _ => ok (.Ok ())
     | .Err error => ok (.Err error)) := by
 rw [NLQ_Stage1Body.result e _ p d _ _ _ tx1]
 exact NLQ_Stage1Fold.result e _ p d
#print owned
#print stage1
#print axioms owned
#print axioms stage1
end NLQ_InstalledStage1
