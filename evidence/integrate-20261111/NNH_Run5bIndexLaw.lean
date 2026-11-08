import NNH_Run5bGeometryUnits
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bIndexLaw
open Aeneas Aeneas.Std Result

def erase {C : Type} (x : Result (core.result.Result Usize C)) :
 Result (core.result.Result Usize AspisR1Stage2.verifier.Error) := do
 let r ← x
 match r with
 | .Ok u => .ok (.Ok u)
 | .Err _ => .ok (.Err .Query)

theorem fibre_admitted {C : Type} (err : C) (u : Usize) (bound : u.val < 262144) :
 SAQ_Constructor.fibre err u = .ok (.Ok u) := by
 unfold SAQ_Constructor.fibre
 have h : u < 262144#usize := bound
 rw [if_pos h]

theorem erase_index {C C' : Type} (err : C) (err' : C') (u : Usize) :
 erase (SAQ_Constructor.fibre err u) = erase (NFN_NEB_GeometryIndices.indexPort err' u) := by
 unfold SAQ_Constructor.fibre NFN_NEB_GeometryIndices.indexPort NEA_Reference.fibre_new_ref
 split <;> rfl

#print axioms fibre_admitted
#print axioms erase_index
end AspisR1.NNH_Run5bIndexLaw
end
