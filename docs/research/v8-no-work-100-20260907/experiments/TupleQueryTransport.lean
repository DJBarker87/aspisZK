import TupleQuerySymbols
import SelectedSupportIdentification

/-! Exact selected zero-check transport. Q and final may be chosen after
alpha; the actual image/original-message and true-fold equalities eliminate
them from the query predicate. The generic core retains the full negative
residual identity. No global no-pole or received polynomiality premise. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 150000

namespace AspisV8.TupleQueryTransport.Generic
open AspisV5ComponentCConcreteFoldLinearity
open AspisV8.FixedTargetQuerySupport
variable {F : Type*} [Field F]

theorem fold_check (x y alpha : F) (received encoded error : Fin 4 → F)
    (four : (4 : F) ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (slots : ∀ j, received j-encoded j=error j) :
    circleFoldValue alpha (2*x)⁻¹ (2*y)⁻¹ encoded =
      circleFoldValue alpha (2*x)⁻¹ (2*y)⁻¹ received ↔
      (foldedPolynomial x y error).eval alpha=0 := by
  have equation := TupleQueryTransportCore.residual_fold x y alpha received encoded error
    four hx hy slots
  rw [← sub_eq_zero, equation, neg_eq_zero]

theorem query_check [DecidableEq F] [NeZero (2 : F)] {q : Nat}
    (final : Fin 256 → F) (queries : Fin q → F) (received : F → F) (j : Fin q) :
    PostQueryFunctional.residual final queries received j=0 ↔
      PostQueryFunctional.lineEval final (queries j)=received (queries j) :=
  sub_eq_zero

theorem fold_check_twiddles (x y alpha ix iy : F) (received encoded error : Fin 4 → F)
    (four : (4 : F) ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (inverseX : 2*x*ix=1) (inverseY : 2*y*iy=1)
    (slots : ∀ j, received j-encoded j=error j) :
    circleFoldValue alpha ix iy encoded=circleFoldValue alpha ix iy received ↔
      (foldedPolynomial x y error).eval alpha=0 := by
  have inverse (a b : F) (h : a*b=1) : b=a⁻¹ := by
    have nonzero : a≠0 := by
      intro zero
      exact zero_ne_one (by simpa only [zero, zero_mul] using h)
    apply mul_left_cancel₀ nonzero
    exact h.trans (mul_inv_cancel₀ nonzero).symm
  rw [inverse (2*x) ix inverseX, inverse (2*y) iy inverseY]
  exact fold_check x y alpha received encoded error four hx hy slots

#print axioms fold_check
#print axioms query_check
#print axioms fold_check_twiddles
end AspisV8.TupleQueryTransport.Generic

namespace AspisV8.TupleQueryTransport
open Polynomial Finset
open AspisV5ComponentCConcreteFoldLinearity
open AspisPool.V7C1ConcreteProjectionBinding
open AspisK1.V7Tag73CanonicalOneFoldSchedule
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.OODInterpolant AspisV8.GammaComponentGame
open AspisV8.SelectedReceivedOracle AspisV8.FixedTargetQuerySupport
noncomputable section
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

theorem fold_zero_iff (c1 : C1Received) (c2 : C2Received)
    (tuple : Fin 29 → Fin 1024 → K) (data : Data (K := K))
    (checked : data.Checked) (gamma alpha : K) (Q : Fin 1024 → K)
    (image : Q 1023=0 ∧ (atGamma data gamma).b*Q 1022-(atGamma data gamma).c*Q 1021=0)
    (represented : (atGamma data gamma).original Q=ClaimTransport.batch gamma tuple)
    (final : Fin 256 → K) (identified : final=coefficientFoldLayer 256 alpha Q)
    (i : Fin 262144) (legal : Legal data i) :
    exactFinalLinear final i=circleFoldLayer 262144 alpha
      (canonicalOneFoldSchedule 0).circleInv2x (canonicalOneFoldSchedule 0).circleInv2y
      (SelectedComponentGame.received c1 c2 data gamma) i ↔
    (fibreFold exactCircleX exactCircleY (denominators data) (errors c1 c2 tuple) i gamma).eval alpha=0 := by
  rw [identified, ← congrFun (SelectedSupportIdentification.selected_fold_commutes Q alpha) i]
  rw [circleFoldLayer_apply, circleFoldLayer_apply]
  have slots : ∀ j : Fin 4,
      SelectedComponentGame.received c1 c2 data gamma (childIndex i j)-
        exactInitialEncoder Q (childIndex i j)=
          (errors c1 c2 tuple i j).eval gamma / denominators data i j := by
    intro j
    dsimp only [errors, denominators]
    exact symbol_transport c1 c2 tuple data checked gamma Q image represented
      (childIndex i j) (legal j)
  have inverse := canonical_one_fold_schedule_exact 0
  have transported := Generic.fold_check_twiddles
    (exactCircleX i) (exactCircleY i) alpha
    (algebraMap AspisV5ComponentCQM31TowerExact.M31Exact K
      ((canonicalOneFoldSchedule 0).circleInv2x i))
    (algebraMap AspisV5ComponentCQM31TowerExact.M31Exact K
      ((canonicalOneFoldSchedule 0).circleInv2y i))
    (fun j => SelectedComponentGame.received c1 c2 data gamma (childIndex i j))
    (fun j => exactInitialEncoder Q (childIndex i j))
    (fun j => (errors c1 c2 tuple i j).eval gamma / denominators data i j)
    four_nonzero (x_nonzero i) (y_nonzero i) (inverse.1 i) (inverse.2 i) slots
  simpa only [fibreFold] using transported

theorem query_zero_iff {q : Nat} (c1 : C1Received) (c2 : C2Received)
    (tuple : Fin 29 → Fin 1024 → K) (data : Data (K := K))
    (checked : data.Checked) (gamma alpha : K) (Q reference : Fin 1024 → K)
    (image : Q 1023=0 ∧ (atGamma data gamma).b*Q 1022-(atGamma data gamma).c*Q 1021=0)
    (represented : (atGamma data gamma).original Q=ClaimTransport.batch gamma tuple)
    (final : Fin 256 → K) (identified : final=coefficientFoldLayer 256 alpha Q)
    (queries : Fin q → Fin 262144) (j : Fin q) (legal : Legal data (queries j)) :
    PostQueryFunctional.residual final (fun t => PostQueryFunctional.storedPoint (K := K) (queries t))
      ((oracle reference (SelectedComponentGame.received c1 c2 data gamma)).folded alpha) j=0 ↔
    (fibreFold exactCircleX exactCircleY (denominators data) (errors c1 c2 tuple)
      (queries j) gamma).eval alpha=0 := by
  rw [Generic.query_check, SelectedReceivedOracle.final_evaluation final (queries j),
    SelectedReceivedOracle.oracle_folded reference
      (SelectedComponentGame.received c1 c2 data gamma) alpha (queries j)]
  exact fold_zero_iff c1 c2 tuple data checked gamma alpha Q image represented
    final identified (queries j) legal

#print axioms fold_zero_iff
#print axioms query_zero_iff
end
end AspisV8.TupleQueryTransport
