import R1Z.PV_RDB2D_SparseEntries
namespace R1Z.PV_RDB2D_SparseWeights
open Aeneas Aeneas.Std Result PV_RDB2D_SparseFold
set_option autoImplicit false
structure WeightOps (K : Type) extends Ops K where
  one : K
  subOne : K → Result K

def step {K : Type} (ops : WeightOps K) (width pref : Nat) (acc : K × Nat) (coordinate : K) : Result (K × Nat) := do
  let factor ← if pref.testBit (width-1-acc.2) then ok coordinate else ops.subOne coordinate
  let weight ← ops.mul acc.1 factor
  ok (weight,acc.2+1)

def source {K : Type} (ops : WeightOps K) (width pref : Nat) : List K → K × Nat → Result (K × Nat)
  | [],acc => ok acc
  | coordinate::tail,acc => do
    let next ← step ops width pref acc coordinate
    source ops width pref tail next

def reference {K : Type} (ops : WeightOps K) (width pref : Nat) (coordinates : List K) (acc : K × Nat) : Result (K × Nat) :=
  coordinates.foldlM (step ops width pref) acc

theorem all_coordinates {K : Type} (ops : WeightOps K) (width pref : Nat)
    (coordinates : List K) (acc : K × Nat) :
    source ops width pref coordinates acc=reference ops width pref coordinates acc := by
  induction coordinates generalizing acc with
  | nil => rfl
  | cons coordinate tail ih =>
    simp only [source,reference,List.foldlM_cons]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro next _
    exact ih next

def build {K : Type} (ops : WeightOps K) (point : List K) (width trailing suffix : Nat) : Result (List (Entry K)) :=
  (List.range (2^width)).mapM fun pref => do
    let (weight,_) ← source ops width pref (point.take width) (ops.one,0)
    ok (PV_RDB2D_SparseAddress.row pref trailing suffix,weight)

#print axioms all_coordinates
end R1Z.PV_RDB2D_SparseWeights
