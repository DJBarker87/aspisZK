import R1Z.PV_V263_Range
/-! Public source-level request shapes, not an allocator or OS adequacy claim.
Capacities count elements, not allocator requests: Vec may use zero-size
specialisation or grow its handles buffer, and spawn has its own allocations.
These distinctions are part of the named V400 obligation below. -/
set_option autoImplicit false
namespace R1Z.PV_V263_PublicRequests
open PV_RunJoin_WorkRange35

structure Layout where
  size : Nat
  align : Nat
 deriving DecidableEq

structure Shape where
  count : Nat
  nested : Bool
  element : Layout
  family : Layout
  caught : Layout
  handle : Layout
 deriving DecidableEq

inductive Capacity where
  | item (worker elements : Nat) (layout : Layout)
  | outer (elements : Nat) (layout : Layout)
  | handlesPush (length : Nat) (layout : Layout)
  | caught (elements : Nat) (layout : Layout)
  | families (elements : Nat) (layout : Layout)
 deriving DecidableEq

/-- Source capacity sites in merge order; not a chronological thread trace. -/
def capacities (s : Shape) : List Capacity :=
  (List.range 16).map (fun k => .item k (width s.count k) s.element) ++
  (if s.nested then [] else
    (List.range' 1 15).map (fun k => .handlesPush k s.handle) ++
    [.caught 16 s.caught]) ++
  [.families 16 s.family, .outer s.count s.element]

def threads (s : Shape) : List Nat := if s.nested then [] else List.range' 1 15

/-- Byte payload of an explicit capacity, before allocator rounding and headers.
The handlesPush length is NOT its capacity; growth policy is deliberately
left to the named obligation. -/
def bytes : Capacity → Nat
  | .item _ n l | .outer n l | .handlesPush n l | .caught n l | .families n l => n*l.size

/-- The request-shape functions have no witness argument. To use this fact for
actual calls one must establish equality of their public Shape values. -/
theorem same_public (s t : Shape) (h : s = t) :
    threads s = threads t ∧ capacities s = capacities t ∧
    (capacities s).map bytes = (capacities t).map bytes := by
  subst t
  exact ⟨rfl,rfl,rfl⟩

theorem nonnested_threads (s : Shape) (h : s.nested = false) :
    (threads s).length = 15 := by simp only [threads,h,Bool.false_eq_true,if_false,List.length_range']

theorem nested_threads (s : Shape) (h : s.nested = true) : threads s = [] := by
  simp only [threads,h,if_true]

theorem family_sum (n : Nat) :
    (PV_RunJoin_WorkCoverage35.indices n 16).length = n :=
  PV_RunJoin_WorkCoverage35.count n

/-- Exact boundary for rdea-2(b). The arguments are executions with the same
public input, possibly different witnesses. A proof must instantiate these
predicates from the source, not assume this structure at the privacy endpoint.
No new T field is introduced. -/
structure V400Obligation (Execution Public Witness Request Answer Observation : Type)
    (publicOf : Execution → Public) (witnessOf : Execution → Witness)
    (requests : Execution → List Request) (answers : Execution → List Answer)
    (failureObservation : Execution → Observation) : Prop where
  public_requests : ∀ x y, publicOf x = publicOf y → requests x = requests y
  public_answers : ∀ x y, publicOf x = publicOf y → requests x = requests y → answers x = answers y
  public_failure_timing : ∀ x y, publicOf x = publicOf y →
    requests x = requests y → answers x = answers y → failureObservation x = failureObservation y

/-- This implication exposes all three missing source/runtime facts; it does
not discharge them. witnessOf is present to pin the intended execution family. -/
theorem failure_independent {E P W R A O : Type}
    (p : E → P) (w : E → W) (r : E → List R) (a : E → List A) (o : E → O)
    (bound : V400Obligation E P W R A O p w r a o)
    (x y : E) (same : p x = p y) : o x = o y :=
  bound.public_failure_timing x y same (bound.public_requests x y same)
    (bound.public_answers x y same (bound.public_requests x y same))

#print axioms capacities
#print axioms threads
#print axioms bytes
#print axioms same_public
#print axioms nonnested_threads
#print axioms nested_threads
#print axioms family_sum
#print axioms V400Obligation
#print axioms failure_independent
end R1Z.PV_V263_PublicRequests
