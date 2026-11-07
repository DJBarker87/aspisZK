import NFY_Part057
import NMS_AllocationRegular
set_option autoImplicit false
noncomputable section
namespace NMS_ReconstructSites
open Aeneas Aeneas.Std AdapterRw
attribute [local instance] Classical.propDecidable
abbrev Request := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
abbrev Auth := r1_pool_adapter.AuthenticatedAsq8Accounts
abbrev Candidate := aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1

def asset (r : Request) : U32 :=
 match r.«public» with | .PrivateTransfer p => p.asset_id | .Withdrawal p => p.asset_id

def reaches_boxes (r : Request) (a : Auth) (c : Candidate) : Prop :=
 a.live_snapshot.next_pair_index.val + 1 = c.next_pair_index.val ∧ a.master.identity.asset_id = asset r

/-- Source sites r1_pool_adapter.rs:874/asq8_common:814 and statement_box:832
or849: both allocations precede statement validation. They have no observable
intermediate event, but each stop carries only the prefix. -/
def meaning (r : Request) (a : Auth) (c : Candidate) : RSL.Spec
 (core.result.Result aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
  solana_program_error.ProgramError) :=
 if reaches_boxes r a c then
  RSL.Spec.bind RSL.Spec.alloc (fun _ => RSL.Spec.bind RSL.Spec.alloc
   (fun _ => NMS_Interpreted.liftResult (AspisR1.NFY_JHf_ReconstructionSlot.source r a c)))
 else NMS_Interpreted.liftResult (AspisR1.NFY_JHf_ReconstructionSlot.source r a c)

/-- Every normal result is the exact CLOSED reconstruction source result;
private allocation aborts do not acquire an invented returned statement. -/
theorem regular (r : Request) (a : Auth) (c : Candidate) :
 NMS_Regular.Law (meaning r a c) (AspisR1.NFY_JHf_ReconstructionSlot.source r a c) := by
 unfold meaning
 split
 · apply NMS_AllocationRegular.bind
   apply NMS_AllocationRegular.bind
   exact NMS_Regular.lift _
 · exact NMS_Regular.lift _
#print axioms regular
end NMS_ReconstructSites
