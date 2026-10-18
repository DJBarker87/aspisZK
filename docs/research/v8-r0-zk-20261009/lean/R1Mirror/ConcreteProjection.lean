import R1Mirror.Line18Geometry
import R1Mirror.ParentSupport
import Wide.FinalEncoder

/-! Concrete log-18/log-16 encoder identities and complete-quartet descent.
No proximity decoder, protocol acceptance, source correspondence or security
claim is assumed or concluded by this file. -/

set_option autoImplicit false
noncomputable section
namespace AspisR1.ConcreteProjection

open scoped BigOperators
open AspisCircleGroupOrder AspisCircleTensorBinding
open AspisV5FriReleasedLineGeometry AspisV7ExactOneFoldDomains
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriCoherentCandidateExtraction
open AspisWide.FinalEncoder

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K]

abbrev SmallMessage (K : Type) := Fin 64 → K
abbrev SmallWord (K : Type) := Fin 65536 → K

/-- Natural 64-coefficient evaluator at the concrete stored log-16 nodes. -/
def secondEncoder (m : SmallMessage K) : SmallWord K :=
  fun i => AspisR1.naturalEval m (algebraMap (ZMod P) K (storedLine16X i))

theorem four_ne_zero : (4 : K) ≠ 0 := by
  have h2 := AspisWide.InitialEncoder.two_ne_zero (K := K)
  simpa only [show (2 : K) * 2 = 4 by norm_num] using mul_ne_zero h2 h2

/-- Bridge from the existing exact polynomial encoder to the small evaluator. -/
theorem exactFinal_eq_naturalEval (a : Fin 256 → K) (i : Fin 262144) :
    exactFinalEncoder a i = AspisR1.naturalEval a
      (algebraMap (ZMod P) K (storedFirstLineX18 i)) := by
  change (naturalCoefficientPolynomial a).eval _ = _
  rw [naturalCoefficientPolynomial_eval_eq_sum (by norm_num)]
  rfl

theorem exactFinal_sparseLift_child (m : SmallMessage K)
    (i : Fin 65536) (s : Fin 4) :
    exactFinalEncoder (AspisR1.sparseLift m) (AspisR1.childIndex i s) =
      secondEncoder m i := by
  let g := AspisR1.storedLine18_radix4_geometry_algebraMap (K := K)
  have hc := g.child_slot i s
  change algebraMap (ZMod P) K
      (storedFirstLineX18 (AspisR1.childIndex i s)) =
    AspisR1.radix4ChildPoint _ _ s at hc
  rw [exactFinal_eq_naturalEval, hc, AspisR1.sparseLift_eval]
  rw [AspisR1.radix4ChildPoint_t4 _ _ _ _
    (g.t2_x0 i) (g.t2_x1 i) (g.t2_x2 i)]
  rfl

/-- Keeping the low coefficient lane computes the actual encoder fibre mean. -/
theorem exactFinal_projection_mean (a : Fin 256 → K)
    (i : Fin 65536) (s : Fin 4) :
    exactFinalEncoder
        (AspisR1.sparseLift (AspisR1.laneCoefficients 64 0 a))
        (AspisR1.childIndex i s) =
      (∑ t : Fin 4, exactFinalEncoder a (AspisR1.childIndex i t)) / 4 := by
  let g := AspisR1.storedLine18_radix4_geometry_algebraMap (K := K)
  have hc (t : Fin 4) := g.child_slot i t
  change ∀ t : Fin 4, algebraMap (ZMod P) K
      (storedFirstLineX18 (AspisR1.childIndex i t)) =
    AspisR1.radix4ChildPoint _ _ t at hc
  simp_rw [exactFinal_eq_naturalEval, hc]
  exact AspisR1.naturalProjection_eval_fibre_mean (n := 64) four_ne_zero a
    _ _ _ _ (g.t2_x0 i) (g.t2_x1 i) (g.t2_x2 i) s

/-- A message matching a repeated word on at least 64 complete quartets
must have zero non-low lanes, by the existing concrete 255-overlap bound. -/
theorem exactFinal_repeated_descent
    (S : Finset (Fin 65536)) (hS : 64 ≤ S.card)
    (a : Fin 256 → K) (w : SmallWord K)
    (hmatch : ∀ i ∈ S, ∀ s : Fin 4,
      exactFinalEncoder a (AspisR1.childIndex i s) = w i) :
    a = AspisR1.sparseLift (AspisR1.laneCoefficients 64 0 a) := by
  let projected := AspisR1.sparseLift (AspisR1.laneCoefficients 64 0 a)
  have hsubset : AspisR1.fullQuartetSet S ⊆
      agreementSet (exactFinalEncoder a) (exactFinalEncoder projected) := by
    intro k hk
    have hi := AspisR1.parentIndex_mem_of_mem_fullQuartetSet S hk
    simp only [agreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← AspisR1.childIndex_parentIndex_slotIndex k]
    rw [show projected = AspisR1.sparseLift
      (AspisR1.laneCoefficients 64 0 a) from rfl, exactFinal_projection_mean]
    simp_rw [hmatch (AspisR1.parentIndex k) hi]
    simp [four_ne_zero (K := K)]
  by_contra hne
  have upper := exactFinalEncoder_overlap_cap a projected hne
  have lower := Finset.card_le_card hsubset
  rw [AspisR1.fullQuartetSet_card] at lower
  omega

/-- The descended message has the required agreement on the parent support. -/
theorem secondEncoder_of_repeated_match
    (S : Finset (Fin 65536)) (hS : 64 ≤ S.card)
    (a : Fin 256 → K) (w : SmallWord K)
    (hmatch : ∀ i ∈ S, ∀ s : Fin 4,
      exactFinalEncoder a (AspisR1.childIndex i s) = w i) :
    ∀ i ∈ S, secondEncoder (AspisR1.laneCoefficients 64 0 a) i = w i := by
  have hd := exactFinal_repeated_descent S hS a w hmatch
  intro i hi
  have h := hmatch i hi 0
  calc
    secondEncoder (AspisR1.laneCoefficients 64 0 a) i =
        exactFinalEncoder (AspisR1.sparseLift
          (AspisR1.laneCoefficients 64 0 a)) (AspisR1.childIndex i 0) :=
      (exactFinal_sparseLift_child _ _ _).symm
    _ = exactFinalEncoder a (AspisR1.childIndex i 0) := by rw [← hd]
    _ = w i := h

#print axioms four_ne_zero
#print axioms exactFinal_eq_naturalEval
#print axioms exactFinal_sparseLift_child
#print axioms exactFinal_projection_mean
#print axioms exactFinal_repeated_descent
#print axioms secondEncoder_of_repeated_match
end AspisR1.ConcreteProjection
end
