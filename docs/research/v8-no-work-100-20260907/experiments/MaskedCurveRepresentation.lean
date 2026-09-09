import MaskedCurveTail
import ExactFoldRecovery

/-! The curve family's abstract four codewords are exactly one interleaved
circle-lift coefficient vector. Both own support and adaptive final identity
are derived from the actual radix-four encoder/decoder, not assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 100000
namespace AspisV8.MaskedCurveRepresentation
open Finset
open AspisV8.MaskedCurveTail AspisV8.ExactFoldRecovery
open AspisV5FriDegreeThreeCorrelatedAgreement AspisV5FunctionalBatching
open AspisV5ComponentCConcreteFoldLinearity AspisV5FriConcreteEncoderCommutation
open AspisV5FriConcreteEncoderApplicability
noncomputable section
variable {K F : Type*} [Field K] [DecidableEq K] [Field F] [Algebra F K]

def interleave (n : Nat) (components : Fin 4 → Fin n → K) : Fin (4*n) → K :=
  fun index => components (slotIndex index) (parentIndex index)

theorem lane_interleave (n : Nat) (components : Fin 4 → Fin n → K) (lane : Fin 4) :
    coefficientLane n lane (interleave n components)=components lane := by
  funext i
  simp only [coefficientLane_apply,interleave,slotIndex_childIndex,parentIndex_childIndex]

theorem interleave_lanes (n : Nat) (Q : Fin (4*n) → K) :
    interleave n (fun lane => coefficientLane n lane Q)=Q := by
  funext index
  simp only [interleave,coefficientLane_apply,childIndex_parentIndex_slotIndex]

def decodedLanes {m : Nat} (inverse2x inverse2y : Fin m → F)
    (received : Fin (4*m) → K) : Fin 4 → Fin m → K :=
  fun lane i => decodedSlots inverse2x inverse2y received i lane

def fullSupport {n m : Nat} (encoder : (Fin n → K) →ₗ[K] (Fin m → K))
    (x y : Fin m → K) (received : Fin (4*m) → K) (Q : Fin (4*n) → K) : Finset (Fin m) :=
  Finset.univ.filter fun i => ∀ slot : Fin 4,
    circleLiftEncoder encoder x y Q (childIndex i slot)=received (childIndex i slot)

theorem decoded_interleave {n m : Nat} (encoder : (Fin n → K) →ₗ[K] (Fin m → K))
    (x y : Fin m → K) (inverse2x inverse2y : Fin m → F)
    (hx : ∀ i, 2*x i*algebraMap F K (inverse2x i)=1)
    (hy : ∀ i, 2*y i*algebraMap F K (inverse2y i)=1)
    (components : Fin 4 → Fin n → K) (i : Fin m) :
    decodedSlots inverse2x inverse2y
      (circleLiftEncoder encoder x y (interleave n components)) i=
      fun lane => encoder (components lane) i := by
  have slots : (fun slot => circleLiftEncoder encoder x y
      (interleave n components) (childIndex i slot))=
      radix4Evaluate (y i) (-y i) (x i) (fun lane => encoder (components lane) i) := by
    funext slot
    rw [circleLiftEncoder,radix4LiftEncoder_apply_child]
    simp only [Pi.neg_apply,lane_interleave]
  unfold decodedSlots
  rw [slots]
  exact radix4Decode_radix4Evaluate (y i) (-y i) (x i)
    (algebraMap F K (inverse2y i)) (-(algebraMap F K (inverse2y i)))
    (algebraMap F K (inverse2x i)) (hy i)
    (by simpa only [neg_mul,mul_neg,neg_neg] using hy i) (hx i) _

theorem joint_eq_full {n m : Nat} (encoder : (Fin n → K) →ₗ[K] (Fin m → K))
    (x y : Fin m → K) (inverse2x inverse2y : Fin m → F)
    (hx : ∀ i, 2*x i*algebraMap F K (inverse2x i)=1)
    (hy : ∀ i, 2*y i*algebraMap F K (inverse2y i)=1)
    (received : Fin (4*m) → K) (components : Fin 4 → Fin n → K) :
    jointAgreementSet encoder (decodedLanes inverse2x inverse2y received) components=
      fullSupport encoder x y received (interleave n components) := by
  classical
  ext i
  simp only [jointAgreementSet,fullSupport,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro same
    have decoded : decodedSlots inverse2x inverse2y received i=
        fun lane => encoder (components lane) i := funext same
    have inverse := radix4Evaluate_radix4Decode (y i) (-y i) (x i)
      (algebraMap F K (inverse2y i)) (-(algebraMap F K (inverse2y i)))
      (algebraMap F K (inverse2x i)) (hy i)
      (by simpa only [neg_mul,mul_neg,neg_neg] using hy i) (hx i)
      (fun slot => received (childIndex i slot))
    change radix4Evaluate (y i) (-y i) (x i)
      (decodedSlots inverse2x inverse2y received i)=_ at inverse
    rw [decoded] at inverse
    intro slot
    rw [circleLiftEncoder,radix4LiftEncoder_apply_child]
    simpa only [Pi.neg_apply,lane_interleave] using congrFun inverse slot
  · intro same
    have slots : (fun slot => received (childIndex i slot))=
        (fun slot => circleLiftEncoder encoder x y
          (interleave n components) (childIndex i slot)) := funext fun s => (same s).symm
    have decoded : decodedSlots inverse2x inverse2y received i=
        decodedSlots inverse2x inverse2y
          (circleLiftEncoder encoder x y (interleave n components)) i := by
      unfold decodedSlots
      rw [slots]
    rw [decoded_interleave encoder x y inverse2x inverse2y hx hy] at decoded
    exact fun lane => congrFun decoded lane

theorem encoded_curve_eq_fold {n m : Nat} (encoder : (Fin n → K) →ₗ[K] (Fin m → K))
    (components : Fin 4 → Fin n → K) (alpha : K) :
    (fun i => curveValue (fun lane => encoder (components lane)) alpha i)=
      encoder (coefficientFoldLayer n alpha (interleave n components)) := by
  funext i
  rw [encoder_coefficientFoldLayer_apply]
  simp only [lane_interleave,curveValue,batchedDiscrepancy,coefficientFoldValue]
  ring

theorem decoded_curve_actual {m : Nat} (x y : Fin m → K)
    (inverse2x inverse2y : Fin m → F)
    (hx : ∀ i, 2*x i*algebraMap F K (inverse2x i)=1)
    (hy : ∀ i, 2*y i*algebraMap F K (inverse2y i)=1)
    (received : Fin (4*m) → K) (alpha : K) (i : Fin m) :
    curveValue (decodedLanes inverse2x inverse2y received) alpha i=
      circleFoldLayer m alpha inverse2x inverse2y received i := by
  rw [circleFoldLayer_apply,circleFoldValue_eq_coefficientFoldValue_decode alpha
    (x i) (y i) (algebraMap F K (inverse2x i)) (algebraMap F K (inverse2y i))
    (hx i) (hy i)]
  simp only [curveValue,decodedLanes,decodedSlots,batchedDiscrepancy,coefficientFoldValue]
  ring

theorem onCurve_iff {n m : Nat} (encoder : (Fin n → K) →ₗ[K] (Fin m → K))
    (injective : Function.Injective encoder)
    (strategy : ProximateStrategy K (Fin m) (Fin n → K))
    (components : Fin 4 → Fin n → K) (alpha : K) :
    CandidateOnCurve encoder strategy components alpha ↔
      strategy.candidate alpha=coefficientFoldLayer n alpha (interleave n components) := by
  unfold CandidateOnCurve
  rw [encoded_curve_eq_fold]
  exact injective.eq_iff

/-- Concrete family membership is equivalent, including both support and
selected coefficient identity. This is not a correspondence premise. -/
theorem covered_iff {n m : Nat} (encoder : (Fin n → K) →ₗ[K] (Fin m → K))
    (injective : Function.Injective encoder)
    (x y : Fin m → K) (inverse2x inverse2y : Fin m → F)
    (hx : ∀ i, 2*x i*algebraMap F K (inverse2x i)=1)
    (hy : ∀ i, 2*y i*algebraMap F K (inverse2y i)=1)
    (received : Fin (4*m) → K) (a : Nat)
    (strategy : ProximateStrategy K (Fin m) (Fin n → K)) (alpha : K) :
    CoveredAt encoder (decodedLanes inverse2x inverse2y received) a strategy alpha ↔
      ∃ Q : Fin (4*n) → K, a≤(fullSupport encoder x y received Q).card ∧
        strategy.candidate alpha=coefficientFoldLayer n alpha Q := by
  constructor
  · rintro ⟨components,own,onCurve⟩
    refine ⟨interleave n components,?_,(onCurve_iff encoder injective strategy components alpha).mp onCurve⟩
    rwa [joint_eq_full encoder x y inverse2x inverse2y hx hy] at own
  · rintro ⟨Q,own,represented⟩
    refine ⟨(fun lane => coefficientLane n lane Q),?_,?_⟩
    · rw [joint_eq_full encoder x y inverse2x inverse2y hx hy,interleave_lanes]
      exact own
    · apply (onCurve_iff encoder injective strategy _ alpha).mpr
      rwa [interleave_lanes]

end
end AspisV8.MaskedCurveRepresentation
#print axioms AspisV8.MaskedCurveRepresentation.joint_eq_full
#print axioms AspisV8.MaskedCurveRepresentation.onCurve_iff
#print axioms AspisV8.MaskedCurveRepresentation.covered_iff
#print axioms AspisV8.MaskedCurveRepresentation.decoded_curve_actual
