import R1Z.PV_RDB2D_SparseLookup
namespace R1Z.PV_RDB2D_SparseFold
open Aeneas Aeneas.Std Result
set_option autoImplicit false

structure Ops (K : Type) where
  zero : K
  mul : K → K → Result K
  add : K → K → Result K
abbrev Entry (K : Type) := Nat × K

def term {K : Type} (ops : Ops K) (column : List K) (acc : K) (entry : Entry K) : Result K := do
  let value ← PV_RDB2D_SparseLookup.read column entry.1
  let product ← ops.mul entry.2 value
  ops.add acc product

def source {K : Type} (ops : Ops K) (column : List K) : List (Entry K) → K → Result K
  | [],acc => ok acc
  | entry::tail,acc => do
    let next ← term ops column acc entry
    source ops column tail next

def reference {K : Type} (ops : Ops K) (column : List K) (entries : List (Entry K)) (acc : K) : Result K :=
  entries.foldlM (term ops column) acc

/-- Arbitrary columns and raw scalar operations: no constant-column fixture,
canonical-field image, assumed result, or commuting/reordered field calls. -/
theorem arbitrary_column {K : Type} (ops : Ops K) (column : List K)
    (entries : List (Entry K)) (acc : K) :
    source ops column entries acc=reference ops column entries acc := by
  induction entries generalizing acc with
  | nil => rfl
  | cons entry tail ih =>
    simp only [source,reference,List.foldlM_cons]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro next _
    exact ih next

theorem failure_stops_suffix {K : Type} (ops : Ops K) (column : List K)
    (entry : Entry K) (tail : List (Entry K)) (acc : K) (e : Error)
    (h : term ops column acc entry=fail e) : source ops column (entry::tail) acc=fail e := by
  simp only [source,h,bind_tc_fail]

theorem divergence_stops_suffix {K : Type} (ops : Ops K) (column : List K)
    (entry : Entry K) (tail : List (Entry K)) (acc : K)
    (h : term ops column acc entry=div) : source ops column (entry::tail) acc=div := by
  simp only [source,h,bind_tc_div]

#print axioms arbitrary_column
#print axioms failure_stops_suffix
#print axioms divergence_stops_suffix
end R1Z.PV_RDB2D_SparseFold
