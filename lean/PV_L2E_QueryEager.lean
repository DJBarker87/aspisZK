import PV_L2D_QueryDriver
set_option autoImplicit false
namespace PV_L2E_QueryEager
open PV_L2D_QueryScan PV_L2D_QueryDriver

inductive Event where
  | digestBlock (index : Nat)
  | digestAdvance (index : Nat)
  | scanBlock (index : Nat)
  | scan (event : PV_L2D_QueryScan.Event)
  | selectedAdvance (index : Nat)
  | finish (accepted : Nat) (success : Bool)
  deriving DecidableEq, Repr

/-- The host emits all pairs BEFORE entering scan, including the unused
suffix. It never lazily stops hash calls after the 22nd accepted query. -/
def eager : Nat → Nat → List Event
  | _,0 => []
  | k,n+1 => .digestBlock k :: .digestAdvance k :: eager (k+1) n

def drive : Nat → State → List (List Nat) → Driven × List Event
  | _,s,[] => (⟨7,s,0⟩,[])
  | k,s,x::xs =>
    let a := execute s x
    if a.1.1 then
      (⟨k,a.1.2,1⟩,.scanBlock k :: a.2.map Event.scan ++ [.selectedAdvance k])
    else
      let b := drive (k+1) a.1.2 xs
      (⟨b.1.selected,b.1.state,b.1.scanned+1⟩,
        .scanBlock k :: a.2.map Event.scan ++ b.2)

theorem driver_value (k : Nat) (s : State) (blocks : List (List Nat)) :
    (drive k s blocks).1=PV_L2D_QueryDriver.drive k s blocks := by
  induction blocks generalizing k s with
  | nil => rfl
  | cons x xs ih =>
    simp only [drive,PV_L2D_QueryDriver.drive,complete]
    split <;> simp_all only [ih]

/-- The caller absorbs before the eager sequence. Error returns retain that
absorbed state; success alone commits the selected advance into self.state. -/
def run {H : Type} (absorbed : H) (advances : Nat → H)
    (blocks : List (List Nat)) : Result × H × List Event :=
  let d := drive 0 ⟨[],0⟩ blocks
  let result := PV_L2D_QueryDriver.finish d.1
  let ok := decide (d.1.state.accepted.length=22)
  (result,if ok then advances d.1.selected else absorbed,
    eager 0 8 ++ d.2 ++ [.finish d.1.state.accepted.length ok])

theorem eager_prefix {H : Type} (absorbed : H) (advances : Nat → H)
    (blocks : List (List Nat)) :
    ∃ suffix, (run absorbed advances blocks).2.2=eager 0 8 ++ suffix := by
  refine ⟨(drive 0 ⟨[],0⟩ blocks).2 ++
    [.finish (drive 0 ⟨[],0⟩ blocks).1.state.accepted.length
      (decide ((drive 0 ⟨[],0⟩ blocks).1.state.accepted.length=22))],?_⟩
  simp only [run,List.append_assoc]

theorem failure_state {H : Type} (absorbed : H) (advances : Nat → H)
    (blocks : List (List Nat))
    (fail : (drive 0 ⟨[],0⟩ blocks).1.state.accepted.length≠22) :
    (run absorbed advances blocks).2.1=absorbed := by simp [run,fail]

theorem success_state {H : Type} (absorbed : H) (advances : Nat → H)
    (blocks : List (List Nat))
    (ok : (drive 0 ⟨[],0⟩ blocks).1.state.accepted.length=22) :
    (run absorbed advances blocks).2.1=advances (drive 0 ⟨[],0⟩ blocks).1.selected := by
  simp [run,ok]

theorem eager_length (k n : Nat) : (eager k n).length=2*n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp only [eager,List.length_cons,ih]; omega

#print axioms driver_value
#print axioms eager_prefix
#print axioms failure_state
#print axioms success_state
#print axioms eager_length
end PV_L2E_QueryEager
