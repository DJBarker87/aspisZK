import PV_L2D_ScalarPort
import Mathlib.Tactic
set_option autoImplicit false
namespace PV_L2D_ExpanderPort
open PV_L2D_ScalarPort
abbrev Seed := Fin 32 → UInt8
abbrev Cache := Fin 8 → UInt32

structure State where
  seed : Seed
  counter : UInt64
  word : Fin 9
  cache : Cache

inductive WordEvent where
  | refill (yes : Bool)
  | hash (counter : UInt64)
  | counterWrite (counter : UInt64)
  | cursorWrite (word : Nat)
  | load (byteOffset : Nat)
  deriving DecidableEq, Repr

def initial (seed : Seed) : State := ⟨seed,0,⟨8,by decide⟩,fun _ => 0⟩

/-- Cache is the eight little-endian word views of the 32-byte native block.
Hash framing/native decoding is an explicit structural binding obligation.
The seed's value is internal state, not an observable event. -/
def next (hash : Seed → UInt64 → Cache) (s : State) : Draw State WordEvent :=
  let refill := s.word.val=8
  let i : Fin 8 := if h : refill then ⟨0,by decide⟩ else ⟨s.word.val,by have := s.word.isLt;omega⟩
  let cache := if refill then hash s.seed s.counter else s.cache
  let counter := if refill then s.counter+1 else s.counter
  let events := WordEvent.refill (decide refill) ::
    ((if refill then [.hash s.counter,.counterWrite counter,.cursorWrite 0] else []) ++
      [.cursorWrite (i.val+1)] ++ List.ofFn (fun j : Fin 4 => .load (4*i.val+j.val)))
  ⟨cache i,⟨s.seed,counter,⟨i.val+1,by have:=i.isLt;omega⟩,cache⟩,events⟩

theorem seed_unchanged (hash : Seed → UInt64 → Cache) (s : State) :
    (next hash s).after.seed=s.seed := rfl
#print axioms seed_unchanged

theorem cursor_exact (hash : Seed → UInt64 → Cache) (s : State) :
    (next hash s).after.word.val=(if s.word.val=8 then 1 else s.word.val+1) := by
  by_cases h : s.word.val=8 <;> simp [next,h]
#print axioms cursor_exact

theorem cursor_admitted (hash : Seed → UInt64 → Cache) (s : State) :
    1≤(next hash s).after.word.val ∧ (next hash s).after.word.val≤8 := by
  rw [cursor_exact]
  have h:=s.word.isLt
  split <;> omega
#print axioms cursor_admitted

theorem counter_exact (hash : Seed → UInt64 → Cache) (s : State) :
    (next hash s).after.counter=(if s.word.val=8 then s.counter+1 else s.counter) := rfl
#print axioms counter_exact

theorem loads_in_bounds (i : Fin 8) (j : Fin 4) : 4*i.val+j.val<32 := by
  have:=i.isLt;have:=j.isLt;omega
#print axioms loads_in_bounds

/-- The complete next-word control/index trace does not inspect the seed or
cache contents. The scalar caller's acceptance predicate is kept separately. -/
theorem trace_public (left right : Seed → UInt64 → Cache) (s t : State)
    (word : s.word=t.word) (counter : s.counter=t.counter) :
    (next left s).events=(next right t).events := by
  simp only [next,word,counter]
#print axioms trace_public

theorem initial_cursor (seed : Seed) : (initial seed).word.val=8 := rfl
#print axioms initial_cursor

theorem first_refill (hash : Seed → UInt64 → Cache) (seed : Seed) :
    (next hash (initial seed)).word=hash seed 0 ⟨0,by decide⟩ ∧
    (next hash (initial seed)).after.counter=1 ∧
    (next hash (initial seed)).after.word.val=1 := by
  simp [next,initial]
#print axioms first_refill
end PV_L2D_ExpanderPort
