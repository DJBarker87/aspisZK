import NFT_STAGE2_IMPORT
import Port3_Constructor
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGC_Initialization
open Aeneas Aeneas.Std Result VTop_Stages
/-- Complete heap value Result for both reservation outcomes. Allocation
availability remains an observed execution parameter, never an assumption. -/
theorem heap_result {T : Type} (n : Usize) (value : T) (reserved : Bool) :
 OraclePortStdAllocation.filled n value reserved =
 OraclePortStdAllocation.filledSpec n value reserved :=
 OraclePortStdAllocation.filled_exact n value reserved
/-- Exact emitted constructor instruction order, with the concrete child
content semantics installed, including its Allocation branch. -/
theorem constructor (base : Ops) (reserved : Bool) (v : transport.Variant) :
 (Port3_Constructor.installed base reserved).op12 v =
 Port3_Initial.constructor reserved v :=
 Port3_Constructor.installed_constructor base reserved v
/-- SAME successful S2 constructor output; no independent weight vector. -/
theorem accepted (base : Ops) (reserved : Bool) (a : verifier.Accumulator)
 (run : (Port3_Constructor.installed base reserved).op12 .S2=ok (.Ok a)) :
 reserved=true ∧ a.weights.val=List.replicate 64 Port2_Initial.zeroK ∧
 a.rhs=Port2_Initial.zeroE ∧ a.power=Port2_Initial.oneK ∧ a.next=0#usize := by
 rw [constructor] at run
 exact Port3_Initial.accepted_fields base reserved a run
/-- No oracle, digest, or observer event is manufactured on allocation failure. -/
theorem rejection (base : Ops) :
 (Port3_Constructor.installed base false).op12 .S2=
 ok (.Err AdapterRw.aspis_r1_cost_probe.verifier.Error.Allocation) :=
 Port3_Constructor.allocation_rejects base
#print axioms heap_result
#print axioms constructor
#print axioms accepted
#print axioms rejection
end AspisR1.NGC_Initialization
end
