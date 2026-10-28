import Mathlib.Tactic
set_option autoImplicit false
namespace PV_L2D_Coins
abbrev Block := Fin 32 → UInt8
structure State where
  seed : Block
  attempt : UInt32
  stream : UInt8
  counter : UInt64

inductive Event where
  | hash (attempt : UInt32) (stream : UInt8) (counter : UInt64)
  | test (nonzero : Bool)
  deriving DecidableEq, Repr

structure Prefix where
  value : Option Block
  after : State
  consumed : Nat
  events : List Event

def coin (hash : State → Block) (s : State) : Block × State :=
  (hash s,{s with counter:=s.counter+1})

/-- Fuel is an external prefix observation, NOT a native rejection cap.
No artificial fuel guard is emitted. None means the native loop continues. -/
def run (hash : State → Block) : Nat → State → Prefix
  | 0,s => ⟨none,s,0,[]⟩
  | n+1,s =>
    let (v,t):=coin hash s
    if h : v=(fun _=>0) then
      let p:=run hash n t
      ⟨p.value,p.after,p.consumed+1,
        .hash s.attempt s.stream s.counter :: .test false :: p.events⟩
    else ⟨some v,t,1,[.hash s.attempt s.stream s.counter,.test true]⟩

def advance : Nat → UInt64 → UInt64
  | 0,c => c
  | n+1,c => advance n (c+1)

theorem seed_fixed (hash : State → Block) (n : Nat) (s : State) :
    (run hash n s).after.seed=s.seed ∧
    (run hash n s).after.attempt=s.attempt ∧
    (run hash n s).after.stream=s.stream := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih =>
    simp only [run,coin]
    split
    · exact ih {s with counter:=s.counter+1}
    · simp
#print axioms seed_fixed

theorem consumed_le (hash : State → Block) (n : Nat) (s : State) :
    (run hash n s).consumed≤n := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih =>
    have h:=ih {s with counter:=s.counter+1}
    simp only [run,coin]
    split <;> simp_all
#print axioms consumed_le

theorem counter_exact (hash : State → Block) (n : Nat) (s : State) :
    (run hash n s).after.counter=advance (run hash n s).consumed s.counter := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [run,coin]
    split
    · exact ih {s with counter:=s.counter+1}
    · rfl
#print axioms counter_exact

theorem complete_prefix (hash : State → Block) (m n : Nat) (s : State)
    (h : (run hash m s).value=none) :
    (run hash (m+n) s).value=(run hash n (run hash m s).after).value ∧
    (run hash (m+n) s).after=(run hash n (run hash m s).after).after ∧
    (run hash (m+n) s).events=(run hash m s).events++(run hash n (run hash m s).after).events := by
  induction m generalizing s with
  | zero => simp [run]
  | succ m ih =>
    by_cases hz : hash s=(fun _=>0)
    · have hp : (run hash m {s with counter:=s.counter+1}).value=none := by
        simpa only [run,coin,dif_pos hz] using h
      have t:=ih {s with counter:=s.counter+1} hp
      simp only [Nat.succ_add,run,coin,dif_pos hz,List.cons_append]
      exact ⟨t.1,t.2.1,congrArg (Event.hash s.attempt s.stream s.counter :: Event.test false :: ·) t.2.2⟩
    · simp only [run,coin,dif_neg hz] at h
      contradiction
#print axioms complete_prefix

theorem zero_continues (n : Nat) (s : State) :
    (run (fun _ _=>0) n s).value=none ∧
    (run (fun _ _=>0) n s).consumed=n := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih => simpa [run,coin] using ih {s with counter:=s.counter+1}
#print axioms zero_continues

theorem nonzero_terminates (s : State) (n : Nat) :
    (run (fun _ _=>1) (n+1) s).value=some (fun _=>1) ∧
    (run (fun _ _=>1) (n+1) s).consumed=1 := by
  have ne : (fun _ : Fin 32=>(1 : UInt8))≠(fun _=>0) := by
    intro h
    have:=congrFun h ⟨0,by decide⟩
    contradiction
  simp [run,coin,ne]
#print axioms nonzero_terminates
end PV_L2D_Coins
