import PV_DIAG4_Leaves
import PV_DIAG4_Once
import PV_DIAG4_Interrupted
/-! Joint diagnostic-emission law for the concrete silent leaves. Return
values are retained as a list: a caller that branches on status/Interrupted
still needs its joint control law. No clock/schedule/timing observer is erased.
The theorem's projection is explicitly diagnostics-only. -/
set_option autoImplicit false
namespace PV_DIAG4
open PV_DIAG3
variable {S : Type}
inductive LeafRequest where
 | status (trace : TraceValue)
 | flush
 | vectored
 | panicOutput
 | osGuard (code : Fin (2^32))
 | osDrop (code : Fin (2^32))
inductive LeafResult where
 | status (status : Status)
 | unit
 | flag (b : Bool)
 | available (b : Bool)
 deriving Repr
def leafResult : LeafRequest → LeafResult
 | .status .unsupported => .status .unsupported
 | .status .disabled => .status .disabled
 | .status (.captured _ _) => .status .captured
 | .flush => .unit
 | .vectored => .flag true
 | .panicOutput => .available true
 | .osGuard c => .flag (c.val == 4)
 | .osDrop _ => .unit
def executeLeaf (request : LeafRequest) : Op S LeafResult :=
 match request with
 | .status trace => sequence (status trace) (fun value => PV_DIAG3.pure (.status value))
 | .flush => sequence rawFlush (fun _ => PV_DIAG3.pure .unit)
 | .vectored => sequence rawIsWriteVectored (fun b => PV_DIAG3.pure (.flag b))
 | .panicOutput => sequence panicOutput (fun out => PV_DIAG3.pure (.available out.isSome))
 | .osGuard c => sequence (osInterrupted c) (fun b => PV_DIAG3.pure (.flag b))
 | .osDrop c => sequence (errorReprDrop (fun _ : Unit => (PV_DIAG3.pure () : Op S Unit)) (.os c))
    (fun _ => PV_DIAG3.pure .unit)
def executeLeaves : List LeafRequest → Op S (List LeafResult)
 | [] => PV_DIAG3.pure []
 | r::rs => sequence (executeLeaf r) (fun value =>
    sequence (executeLeaves rs) (fun values => PV_DIAG3.pure (value::values)))
theorem concrete_leaf_exact (request : LeafRequest) (s : S) :
 executeLeaf request s = ⟨[],s,.value (leafResult request)⟩ := by
 cases request with
 | status trace => cases trace <;> rfl
 | flush => rfl
 | vectored => rfl
 | panicOutput => rfl
 | osGuard c => rfl
 | osDrop c => rfl
#print axioms concrete_leaf_exact
theorem concrete_leaves_exact (requests : List LeafRequest) (s : S) :
 executeLeaves requests s = ⟨[],s,.value (requests.map leafResult)⟩ := by
 induction requests with
 | nil => rfl
 | cons r rs ih =>
   simp [executeLeaves,sequence,concrete_leaf_exact,PV_DIAG3.bind,ih,PV_DIAG3.pure,prepend]
#print axioms concrete_leaves_exact
theorem silent_leaves_emission_joint (actualCount l1Count : Nat)
 (requests : List LeafRequest) (s : S) (existingL1CountLaw : actualCount = l1Count) :
 (actualCount,(executeLeaves requests s).events) = (l1Count,([] : List Event)) := by
 rw [concrete_leaves_exact,existingL1CountLaw]
#print axioms silent_leaves_emission_joint
theorem silent_leaves_return_control_retained (requests : List LeafRequest) (s : S)
 (next : List LeafResult → Op S Unit) :
 sequence (executeLeaves requests) next s = next (requests.map leafResult) s := by
 simp [sequence,concrete_leaves_exact,PV_DIAG3.bind,prepend]
#print axioms silent_leaves_return_control_retained
end PV_DIAG4
