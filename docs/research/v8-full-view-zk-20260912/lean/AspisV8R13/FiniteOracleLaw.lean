import AspisV8R13.MovingLeaves
import AspisV8H1C2.FiniteTransport
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

set_option autoImplicit false
namespace AspisV8R13
noncomputable section
variable {C D Index Key Digest : Type*}
variable [DecidableEq Index] [DecidableEq Key]
variable [Fintype C] [Fintype D] [Fintype Index] [Fintype Key] [Fintype Digest]
variable [Nonempty C] [Nonempty D] [Nonempty Digest]

/-- Exact equality for the COMPLETE output pair: transformed coins and the
complete oracle. Testing only roots or conditioning on no hits is unnecessary
for this marginal identity. Visibility and first-hit accounting are separate. -/
theorem moving_leaf_full_uniform_law
    (left : C → Index → Key) (right : D → Index → Key)
    (move : (Index → Digest) → C ≃ D) :
    AspisV8H1C2.SameUniformLaw
      (movingLeafEquiv left right move)
      (fun world : D × LeafOracle Index Key Digest => world) := by
  exact AspisV8H1C2.sameUniformLaw_of_equiv _ _
    (movingLeafEquiv left right move) (fun _ => rfl)


/-- The source-selected full leaf answers have the same joint law with the
coins as evaluations at fixed addresses. Together with the elementary product
law of disjoint function cells, this is the opaque-commitment independence
fact. It says nothing about an observer also reading the moved oracle cells. -/
theorem selected_answers_fixed_address_law
    (left : C → Index → Key) (anchor : Index → Key) :
    AspisV8H1C2.SameUniformLaw
      (fun world : C × LeafOracle Index Key Digest =>
        (world.1, selected world.2 (left world.1)))
      (fun world : C × LeafOracle Index Key Digest =>
        (world.1, selected world.2 anchor)) := by
  let e : (C × LeafOracle Index Key Digest) ≃
      (C × LeafOracle Index Key Digest) :=
    movingLeafEquiv left (fun _ : C => anchor)
      (fun _ => Equiv.refl C)
  apply AspisV8H1C2.sameUniformLaw_of_equiv _ _ e
  intro world
  change (world.1, selected
    (oracleMove left (fun _ : C => anchor) (fun _ => Equiv.refl C) world).2
    anchor) = (world.1, selected world.2 (left world.1))
  rw [oracleMove_handles]

#print axioms selected_answers_fixed_address_law

#print axioms moving_leaf_full_uniform_law
end
end AspisV8R13
