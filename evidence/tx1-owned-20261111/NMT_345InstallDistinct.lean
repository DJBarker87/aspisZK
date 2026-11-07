import NMT_345Boundary01
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Concrete CLOSED implementation, not a free Ops dictionary. -/
def installDistinct (c : Calls) : Calls :=
 {c with
  c15 := fun a =>
   mapOuter (mapCore id fromPE)
    (AdapterRw.r1_pool_adapter.owned.require_distinct_accounts
     (NGL_ReadonlyModel.install baseOps) (oldArray a))}

/-- Install CLOSED339 at its actual call occurrence, carrying the same
parent and suffix. The only array has its count3 by construction. -/
theorem install_distinct {W : Type} (c : Calls) (s : Selected W) :
 rawSelected (installDistinct c) s =
 tryStep (mapOuter (mapCore id fromPE)
  (NGL_DistinctInduction.reference (oldArray (selectedArray s))))
  (fun _ => raw00 (installDistinct c) s) := by
 rw [boundary_distinct]
 change distinctStep s (raw00 (installDistinct c)) = _
 exact distinct_closed _ _
#print axioms install_distinct
end NMT_345
