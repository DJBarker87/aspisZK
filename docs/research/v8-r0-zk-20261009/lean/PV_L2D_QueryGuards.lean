import PV_L2D_QueryScan
set_option autoImplicit false
namespace PV_L2D_QueryGuards
open PV_L2D_QueryScan
inductive Guard where
  | accepted (stop : Bool)
  | draws (stop : Bool)
  deriving DecidableEq, Repr

def core (s : State) : Bool × List Guard :=
  if s.accepted.length=22 then (true,[.accepted true])
  else (decide (s.draws=64),[.accepted false,.draws (decide (s.draws=64))])

def host (s : State) : Bool × List Guard :=
  if s.draws=64 then (true,[.draws true])
  else (decide (s.accepted.length=22),[.draws false,.accepted (decide (s.accepted.length=22))])

theorem core_value (s : State) : (core s).1=stopped s := by
  by_cases ha : s.accepted.length=22 <;> by_cases hd : s.draws=64 <;> simp [core,stopped,ha,hd]
#print axioms core_value

theorem host_value (s : State) : (host s).1=stopped s := by
  by_cases ha : s.accepted.length=22 <;> by_cases hd : s.draws=64 <;> simp [host,stopped,ha,hd]
#print axioms host_value

/-- The orders differ natively; no trace equality is claimed from equal
Boolean results. Both are explicit functions of the retained scanner state. -/
theorem traces_differ : (core ⟨List.range 22,22⟩).2≠(host ⟨List.range 22,22⟩).2 := by decide
#print axioms traces_differ

def expand : Event → List Guard
  | .wordGuard n d _ => (core ⟨List.replicate n 0,d⟩).2
  | _ => []

theorem expand_exact (s : State) :
    expand (.wordGuard s.accepted.length s.draws (stopped s))=(core s).2 := by
  simp only [expand,core,List.length_replicate]
#print axioms expand_exact

theorem cap_both (s : State) (h : s.accepted.length=22) (d : s.draws=64) :
    core s=(true,[.accepted true]) ∧ host s=(true,[.draws true]) := by
  simp [core,host,h,d]
#print axioms cap_both
end PV_L2D_QueryGuards
