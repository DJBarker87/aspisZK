import NMX_BoxProjection
set_option autoImplicit false
noncomputable section
namespace NMX_AllocationBoundary
open Aeneas Aeneas.Std Result AdapterRw AspisR1

theorem native_divergence {A B S : Type} (f : A → B)
 (allocator : S2W_D189Wrappers.Allocator S) (before : S) (size owner : Nat)
 (reservation : NP6_StdModel.Reservation) (value : A)
 (diverges : allocator.allocate before size = .div) :
 NMX_BoxProjection.observe f
  (NKY_BoxAction.run allocator before size reservation owner (.ok (.Ok value))) =
 ⟨.diverge,[]⟩ := by
 rw [NKY_BoxAction.allocator_divergence allocator before size reservation owner value diverges]
 rfl

/-- Canonical allocation is returning or aborting, not an arbitrary divergent
opaque operation. This is a precise interpretation boundary, not a claim that
an actual runtime allocator diverges. -/
theorem canonical_no_divergence {A : Type} (value : A) (env : RSL.Env) :
 ¬ RSL.RS.bind (RSL.RS.lift RSL.Spec.alloc) (fun _ => RSL.RS.pure value)
  env ⟨.diverge,[]⟩ := by
 intro law
 rcases RSL.RS.alloc_pure_obs value env _ law with returns | aborts
 · have impossible := congrArg RSL.Obs.exit returns
   cases impossible
 · have impossible := congrArg RSL.Obs.exit aborts
   cases impossible
#print axioms native_divergence
#print axioms canonical_no_divergence
end NMX_AllocationBoundary
end
