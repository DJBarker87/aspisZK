import InitialForwardEncoderBaseV9
import InitialMessageComputableV8
import CompPoly.Univariate.ToPoly.Equiv
import CompPoly.Univariate.ToPoly.Impl
import FieldInterpolationNodes

set_option autoImplicit false
namespace AspisWide.InitialMessageForwardFilterV3

open CompPoly
open AspisWide.InitialForwardEncoderBaseV9
open AspisWide.InitialMessageComputableV5
open AspisV5FriCircleEncoderDistance
open AspisV5FriInitialCircleEncoderIdentity

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]
  [NeZero (2 : K)] [Algebra (ZMod AspisCircleGroupOrder.P) K]
  [Fintype K] [LawfulBEq (CPolynomial K)]

/-- Decode with the established V8 inverse and accept only when the actual
CPolynomial forward encoder reconstructs the candidate exactly. -/
def filterMessage (nodes0 : Fin 513 → K) (nodes1 : Fin 512 → K)
    (q : CPolynomial K) : Option (Fin 1024 → K) :=
  let candidate := AspisWide.InitialMessageComputableV1.decodeMessage nodes0 nodes1 q
  if encodeInitialC candidate == q then some candidate else none

theorem filterMessage_sound (nodes0 : Fin 513 → K) (nodes1 : Fin 512 → K)
    (q : CPolynomial K) (m : Fin 1024 → K)
    (h : filterMessage nodes0 nodes1 q = some m) :
    encodeInitialC m = q := by
  simp only [filterMessage] at h
  split at h
  · rename_i hcheck
    injection h with hcandidate
    rw [← hcandidate]
    exact LawfulBEq.eq_of_beq hcheck
  · simp at h

theorem filterMessage_complete_on_image
    (nodes0 : Fin 513 → K) (nodes1 : Fin 512 → K)
    (hinj0 : Function.Injective nodes0) (hinj1 : Function.Injective nodes1)
    (havoid0 : ∀ i, nodes0 i ≠ -1) (havoid1 : ∀ i, nodes1 i ≠ -1)
    (m : Fin 1024 → K) :
    filterMessage nodes0 nodes1 (encodeInitialC m) = some m := by
  unfold filterMessage
  rw [decodeMessage_of_circleNumerator nodes0 nodes1 hinj0 hinj1 havoid0 havoid1
    (encodeInitialC m) m (by rw [encodeInitialC_toPoly])]
  simp

def publicNodes0 : Fin 513 → K :=
  AspisWide.FieldInterpolationNodes.nodes (K := K) 513

def publicNodes1 : Fin 512 → K :=
  AspisWide.FieldInterpolationNodes.nodes (K := K) 512

def filterPublic (q : CPolynomial K) : Option (Fin 1024 → K) :=
  filterMessage publicNodes0 publicNodes1 q

theorem filterPublic_complete_on_image [CharP K AspisCircleGroupOrder.P]
    (h513 : 513 < AspisCircleGroupOrder.P) (h512 : 512 < AspisCircleGroupOrder.P)
    (m : Fin 1024 → K) :
    filterPublic (encodeInitialC m) = some m := by
  unfold filterPublic
  exact filterMessage_complete_on_image publicNodes0 publicNodes1
    (AspisWide.FieldInterpolationNodes.nodes_injective (K := K)
      (p := AspisCircleGroupOrder.P) (n := 513) h513)
    (AspisWide.FieldInterpolationNodes.nodes_injective (K := K)
      (p := AspisCircleGroupOrder.P) (n := 512) h512)
    (AspisWide.FieldInterpolationNodes.nodes_avoid_neg_one (K := K)
      (p := AspisCircleGroupOrder.P) (n := 513) h513)
    (AspisWide.FieldInterpolationNodes.nodes_avoid_neg_one (K := K)
      (p := AspisCircleGroupOrder.P) (n := 512) h512) m

#print axioms filterMessage_sound
#print axioms filterMessage_complete_on_image
#print axioms filterPublic_complete_on_image

end AspisWide.InitialMessageForwardFilterV3
