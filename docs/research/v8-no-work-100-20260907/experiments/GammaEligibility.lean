import NearGammaDichotomy

/-! Generic filter interfaces keep the selected concrete field's existential
predicate opaque. Do not normalize an enumeration of the code or field. -/
set_option autoImplicit false
namespace AspisV8.GammaEligibility
open Polynomial Finset AspisV8.NearGammaDichotomy
variable {K Pos Slot : Type*} [Field K] [DecidableEq K] [DecidableEq Pos]
  [Fintype Slot] [DecidableEq Slot] [DecidableEq (Slot → K)]

theorem good_subset (C : Submodule K (Word (K:=K) (Pos:=Pos) (Slot:=Slot)))
    (D : Finset Pos) (v : Pos → Slot → K[X]) (B : Nat) (G : Finset K) :
    good C D v B G⊆G := by
  classical
  exact Finset.filter_subset _ _

theorem good_mem (C : Submodule K (Word (K:=K) (Pos:=Pos) (Slot:=Slot)))
    (D : Finset Pos) (v : Pos → Slot → K[X]) (B : Nat) (G : Finset K)
    (gamma : K) (hg : gamma∈G) (u : Word (K:=K) (Pos:=Pos) (Slot:=Slot))
    (near : IsNear C D v B gamma u) : gamma∈good C D v B G := by
  classical
  exact Finset.mem_filter.mpr ⟨hg,u,near⟩

#print axioms good_subset
#print axioms good_mem
end AspisV8.GammaEligibility
