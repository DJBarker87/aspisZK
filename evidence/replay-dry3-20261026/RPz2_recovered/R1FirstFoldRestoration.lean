import R1FirstFold
import R1ParentSupport
import R1FoldCoefficientBridge
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Wide.EncoderLinearity

/-! Pointwise restoration of the first-fold input on complete quartets above
any support where all four first-fold channels match the four encoded
messages. This is an algebraic implication only. -/

set_option autoImplicit false

namespace AspisR1.FirstFoldRestoration

open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisWide.Agreement
open AspisWide.InitialEncoder
open AspisWide.FinalEncoder
open AspisCircleGroupOrder

noncomputable section

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K]

/-- Interleave the four final messages into the original first-fold message. -/
def join (a : Fin 4 → FinalMessage K) : InitialMessage K :=
  fun k => a (AspisR1.slotIndex (n := 256) k)
    (AspisR1.parentIndex (n := 256) k)

theorem coefficientLane_join (a : Fin 4 → FinalMessage K) (s : Fin 4) :
    coefficientLane 256 s (join a) = a s := by
  funext i
  rw [AspisV5FriConcreteEncoderCommutation.coefficientLane_apply]
  change a (AspisR1.slotIndex (n := 256)
      (AspisV5ComponentCConcreteFoldLinearity.childIndex i s))
    (AspisR1.parentIndex (n := 256)
      (AspisV5ComponentCConcreteFoldLinearity.childIndex i s)) = a s i
  rw [show AspisV5ComponentCConcreteFoldLinearity.childIndex i s =
    AspisR1.childIndex i s from rfl]
  simp only [AspisR1.slotIndex_childIndex, AspisR1.parentIndex_childIndex]

/-- Folding the interleaved message gives the released final message curve. -/
theorem fold_join (a : Fin 4 → FinalMessage K) (alpha : K) :
    AspisR1.FirstFold.foldMessage alpha (join a) =
      AspisWide.Agreement.exactFinalMessageCurve a alpha := by
  rw [AspisR1.FirstFold.foldMessage,
    AspisR1.FoldCoefficientBridge.coefficientFoldLayer_eq_primalFold
      (n := 256)]
  funext i
  simp only [AspisR1.RoundPairing.primalFold, join,
    AspisR1.slotIndex_childIndex, AspisR1.parentIndex_childIndex,
    AspisWide.Agreement.exactFinalMessageCurve, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- On all child indices above `M`, the initial word is exactly the released
initial encoding of the interleaving of the four matching messages. -/
theorem restore (R : InitialWord K) (a : Fin 4 → FinalMessage K)
    (M : Finset (Fin 262144))
    (ha : M ⊆ jointAgreementSet exactFinalEncoder
      (AspisR1.FirstFold.channels R) a) :
    ∀ k ∈ AspisR1.fullQuartetSet M,
      R k = exactInitialEncoder (join a) k := by
  intro k hk
  let i : Fin 262144 := AspisR1.parentIndex (n := 262144) k
  let s : Fin 4 := AspisR1.slotIndex (n := 262144) k
  have hi_mem : AspisR1.parentIndex (n := 262144) k ∈ M := by
    exact AspisR1.parentIndex_mem_of_mem_fullQuartetSet
      (n := 262144) M hk
  have hmatch : ∀ t : Fin 4,
      AspisR1.FirstFold.channels R t i = exactFinalEncoder (a t) i := by
    have hset := ha hi_mem
    simpa only [jointAgreementSet, Finset.mem_filter, Finset.mem_univ,
      true_and] using hset
  have hencoded : ∀ t : Fin 4,
      AspisR1.FirstFold.channels (exactInitialEncoder (join a)) t i =
        exactFinalEncoder (a t) i := by
    intro t
    rw [AspisR1.FirstFold.encoded_channels,
      coefficientLane_join (K := K) a t]
  have hchannels :
      (fun t => AspisR1.FirstFold.channels R t i) =
      (fun t => AspisR1.FirstFold.channels (exactInitialEncoder (join a)) t i) := by
    funext t
    exact (hmatch t).trans (hencoded t).symm
  have hfibre :
      AspisR1.FirstFold.fibre R i =
      AspisR1.FirstFold.fibre (exactInitialEncoder (join a)) i := by
    apply (AspisR1.FirstFold.fibre_inverse i).2.injective
    simpa only [AspisR1.FirstFold.channels] using hchannels
  have hindex : AspisR1.childIndex i s = k := by
    change AspisR1.childIndex i s = k
    exact AspisR1.childIndex_parentIndex_slotIndex (n := 262144) k
  have hchild :
      AspisV5ComponentCConcreteFoldLinearity.childIndex i s =
        AspisR1.childIndex i s := rfl
  calc
    R k = AspisR1.FirstFold.fibre R i s := by
      change R k = R (AspisR1.childIndex i s)
      rw [hindex]
    _ = AspisR1.FirstFold.fibre (exactInitialEncoder (join a)) i s :=
      congrFun hfibre s
    _ = exactInitialEncoder (join a) k := by
      rw [AspisR1.FirstFold.fibre, hchild, hindex]

#print axioms coefficientLane_join
#print axioms fold_join
#print axioms restore

end
end AspisR1.FirstFoldRestoration
