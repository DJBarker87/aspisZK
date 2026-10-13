import R1SecondFoldMatched
import R1SecondFoldRestoration
import R1FirstFoldRestoration
import R1InitialResponses

/-! Deterministic two-fold extraction on the actual stored domains. A support
of 9558 matching first-layer positions gives a tuple from the literal joint
list of the committed words. The matching equations and exclusion of the
three algebraic bad sets are explicit premises. No commitment binding,
query probability, source correspondence, or Fiat--Shamir claim is made. -/

set_option autoImplicit false
noncomputable section
namespace AspisR1.TwoFoldExtraction

open scoped BigOperators
open AspisCircleGroupOrder
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder AspisWide.FinalEncoder AspisWide.Agreement
open AspisV5FriDegreeThreeCorrelatedAgreement AspisV6Width29CorrelatedAgreement

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K]

def batchedWord (W : Fin 29 → InitialWord K) (gamma : K) : InitialWord K :=
  width29CurveValue W gamma

/-- Concrete second-fold matching reconstructs a 256-coefficient message
on every original first-layer position, including when parents repeat. -/
theorem second_fold_extract
    (V : FinalWord K) (alpha : K)
    (hgood : alpha ∉ AspisR1.SecondFoldMatched.secondBad
      (AspisR1.SecondFoldRestoration.channels V))
    (f : AspisR1.ConcreteProjection.SmallMessage K)
    (M : Finset (Fin 262144)) (hM : 9558 ≤ M.card)
    (hmatch : ∀ i ∈ M,
      curveValue (AspisR1.SecondFoldRestoration.channels V) alpha
          (AspisR1.parentIndex i) =
        AspisR1.ConcreteProjection.secondEncoder f (AspisR1.parentIndex i)) :
    ∃ m : FinalMessage K,
      (∀ i ∈ M, V i = exactFinalEncoder m i) ∧
      f = AspisR1.RoundPairing.primalFold (n := 64) alpha m := by
  let S := AspisR1.parentSupport (n := 65536) M
  have hS : 2390 ≤ S.card :=
    AspisR1.parentSupport_card_ge_2390_65536 M hM
  have hvalid : ∀ i ∈ S,
      curveValue (AspisR1.SecondFoldRestoration.channels V) alpha i =
        AspisR1.ConcreteProjection.secondEncoder f i := by
    intro i hi
    have hex : ∃ k ∈ M, AspisR1.parentIndex k = i := by
      simpa only [S, AspisR1.parentSupport, Finset.mem_image] using hi
    obtain ⟨k, hk, rfl⟩ := hex
    exact hmatch k hk
  obtain ⟨b, hb, hf⟩ := AspisR1.SecondFoldMatched.second_match
    (AspisR1.SecondFoldRestoration.channels V) alpha hgood f S hS hvalid
  let m := AspisR1.SecondFoldRestoration.join b
  refine ⟨m, ?_, ?_⟩
  · intro i hi
    exact AspisR1.SecondFoldRestoration.secondFoldRestoration V S b hb i
      (AspisR1.mem_fullQuartetSet_parentSupport (n := 65536) M i hi)
  · funext i
    have hi := congrFun hf i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hi
    rw [hi]
    unfold AspisR1.RoundPairing.primalFold
    apply Finset.sum_congr rfl
    intro s _
    change alpha ^ s.val * b s i =
      b (AspisR1.slotIndex (AspisR1.childIndex i s))
        (AspisR1.parentIndex (AspisR1.childIndex i s)) * alpha ^ s.val
    simp only [AspisR1.slotIndex_childIndex, AspisR1.parentIndex_childIndex,
      mul_comm]

set_option maxRecDepth 4096 in
/-- The extracted terminal message is the twofold coefficient fold of the
gamma-batch of one tuple in the fixed literal list `Lambda W`. -/
theorem two_fold_extract
    (W : Fin 29 → InitialWord K) (V : FinalWord K)
    (gamma alpha0 alpha1 : K) (hgamma_ne : gamma ≠ 0)
    (hgamma : gamma ∉ AspisR1.InitialResponses.B1 W)
    (hfirst : alpha0 ∉ AspisR1.FinalResponses.B6
      (AspisR1.FirstFold.channels (batchedWord W gamma)))
    (hsecond : alpha1 ∉ AspisR1.SecondFoldMatched.secondBad
      (AspisR1.SecondFoldRestoration.channels V))
    (f : AspisR1.ConcreteProjection.SmallMessage K)
    (M : Finset (Fin 262144)) (hM : 9558 ≤ M.card)
    (hmatch0 : ∀ i ∈ M,
      AspisR1.FirstFold.foldWord alpha0 (batchedWord W gamma) i = V i)
    (hmatch1 : ∀ i ∈ M,
      curveValue (AspisR1.SecondFoldRestoration.channels V) alpha1
          (AspisR1.parentIndex i) =
        AspisR1.ConcreteProjection.secondEncoder f (AspisR1.parentIndex i)) :
    ∃ t ∈ AspisR1.InitialResponses.Lambda W,
      f = AspisR1.RoundPairing.primalFold (n := 64) alpha1
        (AspisR1.RoundPairing.primalFold (n := 256) alpha0
          (exactInitialMessageCurve t gamma)) := by
  obtain ⟨m, hm, hf⟩ := second_fold_extract V alpha1 hsecond f M hM hmatch1
  let R := batchedWord W gamma
  let response : AspisR1.FinalResponses.FinalResponse K := (m, M)
  have hv : AspisR1.FinalResponses.AlphaValid
      (AspisR1.FirstFold.channels R) alpha0 response := by
    constructor
    · change 9557 < M.card
      omega
    · intro i hi
      change curveValue (AspisR1.FirstFold.channels R) alpha0 i =
        exactFinalEncoder m i
      rw [AspisR1.FoldCoefficientBridge.curveValue_eq_coefficientFoldValue]
      exact (hmatch0 i hi).trans (hm i hi)
  obtain ⟨a, ha, hma⟩ := AspisR1.FinalResponses.alpha_match
    (AspisR1.FirstFold.channels R) alpha0 hfirst response hv
  let q := AspisR1.FirstFoldRestoration.join a
  have hmq : m = AspisR1.FirstFold.foldMessage alpha0 q :=
    hma.trans (AspisR1.FirstFoldRestoration.fold_join a alpha0).symm
  have hrestore : ∀ k ∈ AspisR1.fullQuartetSet M,
      R k = exactInitialEncoder q k :=
    AspisR1.FirstFoldRestoration.restore R a M ha
  let initialResponse : AspisR1.InitialResponses.InitialResponse K :=
    (q, AspisR1.fullQuartetSet M)
  have hvalid : AspisR1.InitialResponses.GammaValid W gamma initialResponse := by
    constructor
    · change 38229 < (AspisR1.fullQuartetSet M).card
      rw [AspisR1.fullQuartetSet_card]
      omega
    · exact hrestore
  obtain ⟨t, ht, _hs, hq⟩ := AspisR1.InitialResponses.gamma_match
    W gamma hgamma_ne hgamma initialResponse hvalid
  change t ∈ AspisR1.InitialResponses.Lambda W at ht
  refine ⟨t, ht, ?_⟩
  have hmq' : m = AspisR1.RoundPairing.primalFold (n := 256) alpha0 q :=
    hmq.trans (AspisR1.FoldCoefficientBridge.coefficientFoldLayer_eq_primalFold
      (n := 256) alpha0 q)
  change q = exactInitialMessageCurve t gamma at hq
  exact hf.trans (congrArg (AspisR1.RoundPairing.primalFold (n := 64) alpha1)
    (hmq'.trans (congrArg (AspisR1.RoundPairing.primalFold (n := 256) alpha0) hq)))

#print axioms second_fold_extract
#print axioms two_fold_extract
end AspisR1.TwoFoldExtraction
end
