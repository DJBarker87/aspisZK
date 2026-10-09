import RationalCoordinates
import QueriedResidual

/-! Actual selected log20 quotient / log18 final agreement is bounded by259
when its cleared discrepancy is nonzero. The received raw word is the exact
encoding of the supplied original message U, not an arbitrary oracle declared
polynomial. No image premise is used. The two norm-pole fibres are counted
once, inside possibleMatches. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 150000
namespace AspisV8.SelectedRationalMatch
noncomputable section
open Polynomial
open AspisV8.ChordRationalAlgebra AspisV8.ChordRationalDegree
open AspisV8.ChordRationalOOD AspisV8.RationalCoordinates
open AspisV5ComponentCConcreteFoldLinearity AspisV5FriConcreteEncoderCommutation

section GenericFold
variable {F : Type*} [Field F] [NeZero (2:F)] [DecidableEq F]

theorem norm_eval (a b c s : F) :
    (clearedNorm a b c).eval s=norm a b c s (1-s) := by
  simp [clearedNorm,ChordRationalAlgebra.norm,radialS,radialT]

theorem adjugate_eval (a b c s : F) :
    (fun j => (clearedAdjugate a b c j).eval s)=adjugate a b c s (1-s) := by
  funext j
  fin_cases j <;> simp [clearedAdjugate,adjugate,radialS,radialT]

theorem polynomial_fold_source (a b c x y alpha ix iy : F)
    (u : Fin 4 → F[X]) (circle : x^2+y^2=1)
    (hx : 2*x*ix=1) (hy : 2*y*iy=1)
    (nonpole : (clearedNorm a b c).eval (x^2)≠0) :
    circleFoldValue alpha ix iy
      (quotientFibre a b c x y (fun j => (u j).eval (x^2)))=
      rationalFold a b c alpha u (x^2) := by
  have ht : 1-x^2=y^2 := by linear_combination -circle
  have normAt : (clearedNorm a b c).eval (x^2)=norm a b c (x^2) (y^2) := by
    rw [norm_eval,ht]
  have hnorm : norm a b c (x^2) (y^2)≠0 := by rwa [←normAt]
  rw [normalized_fold_cleared a b c x y alpha ix iy hx hy _ hnorm]
  unfold rationalFold
  rw [folded_numerator_eval,product_eval,adjugate_eval,normAt]
  simp only [radialS,radialT,eval_X,eval_sub,eval_one,ht]

end GenericFold

open AspisV5ComponentCQM31TowerExact AspisCircleTensorBinding
open AspisPool.V7C1ConcreteProjectionBinding
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73CanonicalOneFoldSchedule
open AspisV8.OODInterpolant AspisV8.SelectedQuotientOriginal
open AspisV8.PostQueryFunctional AspisV8.ComponentOODBinding
open AspisV8.QueriedResidual
abbrev K := QM31Exact
local instance : NeZero (2:K) := SelectedReceivedOracle.twoNonzero
local instance : DecidableEq K := Classical.decEq K

def radialPoint (i : Fin 262144) : K := radialFromFinal (storedPoint (K:=K) i)

theorem radial_point_eq_square (i : Fin 262144) : radialPoint i=(exactCircleX i)^2 := by
  unfold radialPoint
  rw [storedPoint_source_pi]
  exact radial_from_final_inverse (NeZero.ne (2:K)) ((exactCircleX i)^2)

theorem radial_point_injective : Function.Injective radialPoint :=
  radial_from_final_injective.comp storedPoint_injective

def radialDomain : Finset K := Finset.univ.image radialPoint

theorem radial_domain_card : radialDomain.card=262144 := by
  rw [radialDomain,Finset.card_image_of_injective _ radial_point_injective]
  simp only [Finset.card_univ,Fintype.card_fin]

theorem final_at_radial (final : Fin 256 → K) (i : Fin 262144) :
    (radialFinal final).eval (radialPoint i)=exactFinalLinear final i := by
  rw [radialFinal,radial_polynomial_eval,radialPoint,final_from_radial_inverse]
  rfl

theorem initial_functional (message : Fin 1024 → K) (i : Fin 1048576) :
    exactInitialEncoder message i=circleFunctional (symbolX i) (symbolY i) message :=
  (circleFunctional_apply (symbolX i) (symbolY i) message).symm

theorem fibre_circle (i : Fin 262144) : (exactCircleX i)^2+(exactCircleY i)^2=1 := by
  have h := symbol_circle (childIndex i 0)
  rw [stored_slot_x,stored_slot_y] at h
  exact h

/-- The exact virtual slots, with the source's signs and interpolant, equal
the rational four-slot quotient of the actual raw polynomial's radial lanes.
This identity is total; norm poles need no division cancellation here. -/
theorem virtual_slots (d : Data (K:=K)) (U : Fin 1024 → K) (i : Fin 262144) :
    (fun j => virtual d (exactInitialEncoder U) (childIndex i j))=
      quotientFibre d.a d.b d.c (exactCircleX i) (exactCircleY i)
        (fun j => (radialLanes (U-d.interpolant) j).eval (radialPoint i)) := by
  funext j
  unfold virtual
  rw [initial_functional,initial_functional,←map_sub,←radial_lanes_value]
  rw [denominator,stored_slot_x,stored_slot_y,radial_point_eq_square]
  fin_cases j <;> simp only [xs,ys,quotientFibre,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,neg_sq,
    mul_neg,sub_eq_add_neg]

/-- Exact selected fold, including the canonical inverse tables. The received
word here is explicitly virtual d (encode U), never an arbitrary word supplied
through an unproved polynomiality predicate. -/
theorem nonpole_virtual_fold (d : Data (K:=K)) (U : Fin 1024 → K)
    (alpha : K) (i : Fin 262144)
    (nonpole : (clearedNorm d.a d.b d.c).eval (radialPoint i)≠0) :
    circleFoldLayer 262144 alpha (canonicalOneFoldSchedule 0).circleInv2x
      (canonicalOneFoldSchedule 0).circleInv2y (virtual d (exactInitialEncoder U)) i=
      rationalFold d.a d.b d.c alpha (radialLanes (U-d.interpolant)) (radialPoint i) := by
  rw [circleFoldLayer_apply,virtual_slots]
  rw [radial_point_eq_square] at nonpole ⊢
  exact polynomial_fold_source d.a d.b d.c (exactCircleX i) (exactCircleY i) alpha
    (algebraMap M31Exact K ((canonicalOneFoldSchedule 0).circleInv2x i))
    (algebraMap M31Exact K ((canonicalOneFoldSchedule 0).circleInv2y i))
    (radialLanes (U-d.interpolant)) (fibre_circle i)
    ((canonical_one_fold_schedule_exact 0).1 i)
    ((canonical_one_fold_schedule_exact 0).2 i) nonpole

def matches (d : Data (K:=K)) (U : Fin 1024 → K) (final : Fin 256 → K)
    (alpha : K) (i : Fin 262144) : Prop :=
  exactFinalLinear final i=circleFoldLayer 262144 alpha
    (canonicalOneFoldSchedule 0).circleInv2x (canonicalOneFoldSchedule 0).circleInv2y
    (virtual d (exactInitialEncoder U)) i

def matchingFibres (d : Data (K:=K)) (U : Fin 1024 → K) (final : Fin 256 → K)
    (alpha : K) : Finset (Fin 262144) := Finset.univ.filter (matches d U final alpha)

theorem matching_radial_inside (d : Data (K:=K)) (U : Fin 1024 → K)
    (final : Fin 256 → K) (alpha : K) (i : Fin 262144)
    (matching : matches d U final alpha i) :
    radialPoint i∈possibleMatches radialDomain d.a d.b d.c alpha
      (radialLanes (U-d.interpolant)) (radialFinal final) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,?_⟩
  by_cases pole : (clearedNorm d.a d.b d.c).eval (radialPoint i)=0
  · exact Or.inl pole
  · apply Or.inr
    rw [←nonpole_virtual_fold d U alpha i pole,final_at_radial]
    exact matching.symm

/-- At most257 nonpole matches plus at most2 radial poles. No independent
pole-fibre term is added, and no image validity is assumed. -/
theorem selected_matching_card_le_259 (d : Data (K:=K)) (U : Fin 1024 → K)
    (final : Fin 256 → K) (alpha : K)
    (normNonzero : clearedNorm d.a d.b d.c≠0)
    (different : clearedDiscrepancy d.a d.b d.c alpha
      (radialLanes (U-d.interpolant)) (radialFinal final)≠0) :
    (matchingFibres d U final alpha).card≤259 := by
  have cap := degree255_possible_match_card_le radialDomain d.a d.b d.c alpha
    (radialLanes (U-d.interpolant)) (radialFinal final)
    (radial_lanes_degree (U-d.interpolant)) (radial_final_degree (by omega) final)
    normNonzero different
  exact (indexed_matching_card_le radialPoint radial_point_injective
    (matches d U final alpha) _ (matching_radial_inside d U final alpha)).trans cap

#print axioms norm_eval
#print axioms polynomial_fold_source
#print axioms radial_point_eq_square
#print axioms radial_point_injective
#print axioms radial_domain_card
#print axioms final_at_radial
#print axioms virtual_slots
#print axioms nonpole_virtual_fold
#print axioms matching_radial_inside
#print axioms selected_matching_card_le_259
end
end AspisV8.SelectedRationalMatch
