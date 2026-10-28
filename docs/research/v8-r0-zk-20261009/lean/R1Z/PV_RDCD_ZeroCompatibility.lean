import R1Z.PV_RDCD_ZeroTrace
set_option autoImplicit false
namespace R1Z.PV_RDCD_ZeroCompatibility
open PV_RDCD_ZeroWorld
inductive LegacyEvent where
  | volatileWrite (address value : Nat)
  | compilerFence
  deriving DecidableEq

def legacyTrace : Nat → Nat → List LegacyEvent
  | _,0 => []
  | address,n+1 => [.volatileWrite address 0,.compilerFence] ++ legacyTrace (address+1) n

def erase : Event → LegacyEvent
  | .volatileWrite a v => .volatileWrite a v
  | .asmReadBarrier _ => .compilerFence

/-- A source-trace conversion, not an equality of hardware fences. -/
theorem erase_trace (address n : Nat) :
    (PV_RDCD_ZeroTrace.trace address n).map erase=legacyTrace address n := by
  induction n generalizing address with
  | zero => rfl
  | succ n ih => simp only [PV_RDCD_ZeroTrace.trace,legacyTrace,List.map_append,List.map_cons,List.map_nil,erase,ih]

def upgrade : Nat → List LegacyEvent → List Event
  | _,[] => []
  | _,.volatileWrite a v::xs => .volatileWrite a v::upgrade a xs
  | last,.compilerFence::xs => .asmReadBarrier last::upgrade last xs

/-- Each barrier address is already present in its immediately preceding
volatile write. This source trace adds no address information to that trace. -/
theorem upgrade_trace (last address n : Nat) :
    upgrade last (legacyTrace address n)=PV_RDCD_ZeroTrace.trace address n := by
  induction n generalizing last address with
  | zero => rfl
  | succ n ih =>
    simp only [legacyTrace,List.cons_append,List.nil_append,upgrade,
      PV_RDCD_ZeroTrace.trace,ih]

theorem trace_information (address n address' n' : Nat)
    (h : legacyTrace address n=legacyTrace address' n') :
    PV_RDCD_ZeroTrace.trace address n=PV_RDCD_ZeroTrace.trace address' n' := by
  rw [←upgrade_trace 0 address n,←upgrade_trace 0 address' n',h]

#print axioms erase_trace
#print axioms upgrade_trace
#print axioms trace_information
end R1Z.PV_RDCD_ZeroCompatibility
