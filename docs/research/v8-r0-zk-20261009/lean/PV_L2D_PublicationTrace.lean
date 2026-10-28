import PV_L2D_PublicationIndices
set_option autoImplicit false
namespace PV_L2D_PublicationTrace
open PV_L2D_PublicationIndices
abbrev Trace := List (Nat × Nat)

def bit (b : Bool) : Nat := if b then 1 else 0

/-- Tags 3..9 are the erasing source instrumentation in publication-native.rs.
The index event precedes its comparison event, preserving Rust's argument
and short-circuit evaluation order. -/
def insertion (x pos : Nat) : List Nat → Trace
  | [] => [(3,0),(6,1),(9,pos)]
  | y::ys =>
    if y<x then [(3,1),(5,pos),(4,1)] ++ insertion x (pos+1) ys
    else [(3,1),(5,pos),(4,0),(6,0),(8,pos),(7,bit (decide (y≠x)))] ++
      if y=x then [] else [(9,pos)]

/-- Complete owned scalar-list executor: result and ordered events are
returned together, on every input, including duplicates and empty batches. -/
def execute (folded : Bool) : Nat → List Nat → List Nat → List Nat × Trace
  | _i, out, [] => (out,[(0,0)])
  | i, out, q::xs =>
    let x := if folded then q/4 else q
    let r := execute folded (i+1) (PV_L2D_PublicationIndices.insert x out) xs
    (r.1, [(0,1),(1,bit folded),(2,i)] ++ insertion x 0 out ++ r.2)

theorem erases (folded : Bool) (i : Nat) (out xs : List Nat) :
    (execute folded i out xs).1 = build out (xs.map (fun q => if folded then q/4 else q)) := by
  induction xs generalizing i out with
  | nil => rfl
  | cons x xs ih => exact ih (i+1) (PV_L2D_PublicationIndices.insert (if folded then x/4 else x) out)
#print axioms erases

theorem full_replay (folded : Bool) (i : Nat) (out xs : List Nat) :
    execute folded i out xs =
      (build out (xs.map (fun q => if folded then q/4 else q)),(execute folded i out xs).2) := by
  exact Prod.ext (erases folded i out xs) rfl
#print axioms full_replay

theorem empty_trace (folded : Bool) (i : Nat) (out : List Nat) : execute folded i out [] = (out,[(0,0)]) := rfl
#print axioms empty_trace

theorem query_set_insufficient :
    (execute false 0 [] [0,1]).1=(execute false 0 [] [1,0]).1 ∧
    (execute false 0 [] [0,1]).2≠(execute false 0 [] [1,0]).2 := by decide
#print axioms query_set_insufficient

theorem source_insert_erases (x : Nat) (xs : List Nat) :
    sourceInsert x xs = PV_L2D_PublicationIndices.insert x xs := source_insert x xs
#print axioms source_insert_erases

-- This is the complete owned trace executor. Source-to-reference loop,
-- indexing and Vec primitive correspondence remain separately audited.
end PV_L2D_PublicationTrace
