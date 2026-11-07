import NMT_345Select
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable
/-- SAME exact array, with no domain or successful-child premise. -/
def selectedArray {W : Type} (s : Selected W) : Array Account 3#usize :=
 Array.make 3#usize [s.proofAccount,s.publicAccount,s.checkpointAccount]
def distinctCall {W : Type} (s : Selected W) : Result (core.result.Result Unit PE) :=
 mapOuter (mapCore id fromPE)
  (AdapterRw.r1_pool_adapter.owned.require_distinct_accounts
   (NGL_ReadonlyModel.install baseOps) (oldArray (selectedArray s)))
def distinctStep {W : Type} (s : Selected W) (next : Selected W → Result Ret) : Result Ret :=
 tryStep (distinctCall s) (fun _ => next s)
/-- Install the CLOSED three-account root at this occurrence. Count=3 is
established by construction, rather than a parent hypothesis. -/
theorem distinct_closed {W : Type} (s : Selected W) (next : Selected W → Result Ret) :
 distinctStep s next =
 tryStep (mapOuter (mapCore id fromPE)
   (NGL_DistinctInduction.reference (oldArray (selectedArray s)))) (fun _ => next s) := by
 unfold distinctStep distinctCall
 rw [NHJ_DistinctPacket.three]
#print axioms distinct_closed
end NMT_345
