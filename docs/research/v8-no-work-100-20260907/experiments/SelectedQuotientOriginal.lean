import QuotientOriginalCore
import SelectedReceivedOracle
import PartialFoldRecovery

/-! Actual stored log20 encoder, totalized quotient, and deterministic pole
accounting. No received-word polynomiality, inverse at every unqueried point,
or component-wise recovery is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 25000
namespace AspisV8.SelectedQuotientOriginal
noncomputable section
open Polynomial Finset
open AspisV5ComponentCQM31TowerExact AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriConcreteEncoderCommutation
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV7ExactOneFoldDomains AspisV5FriInitialCircleEncoderIdentity
open AspisV8.OODInterpolant AspisV8.ChordPolynomialImage
open AspisV8.PartialFoldRecovery AspisV8.CausalOrderedRelation
abbrev K := QM31Exact
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

def symbolX (i : Fin 1048576) : K :=
  algebraMap M31Exact K (AspisCircleGroupOrder.X (storedInitialCirclePoint20 i))
def symbolY (i : Fin 1048576) : K :=
  algebraMap M31Exact K (storedInitialCirclePoint20 i).1.2

theorem symbol_circle (i : Fin 1048576) : (symbolX i)^2+(symbolY i)^2=1 := by
  have h := congrArg (algebraMap M31Exact K) (storedInitialCirclePoint20 i).property
  simpa only [AspisCircleGroupOrder.OnCircle,map_add,map_pow,map_one,
    symbolX,symbolY,AspisCircleGroupOrder.X] using h

theorem symbol_west (i : Fin 1048576) : symbolX i≠-1 := by
  intro hz
  apply storedInitialCirclePoint20_x_ne_neg_one i
  apply FaithfulSMul.algebraMap_injective M31Exact K
  simpa only [symbolX,map_neg,map_one] using hz

def parameter (i : Fin 1048576) : K :=
  algebraMap M31Exact K ((storedInitialCirclePoint20 i).1.2/
    (1+AspisCircleGroupOrder.X (storedInitialCirclePoint20 i)))

theorem parameter_eq (i : Fin 1048576) : parameter i=symbolY i/(1+symbolX i) := by
  simp only [parameter,symbolX,symbolY,map_div₀,map_add,map_one]

theorem parameter_injective : Function.Injective parameter :=
  exactInitialEncoderCircleRealization.parameter_injective

def denominator (d : Data (K := K)) (i : Fin 1048576) : K :=
  d.a+d.b*symbolX i+d.c*symbolY i

/-- These are exactly the fixed-point encoded interpolant values, not an
unrelated convenient anchor. Division remains total at poles. -/
def virtual (d : Data (K := K)) (received : Fin 1048576 → K) : Fin 1048576 → K :=
  fun i => (received i-exactInitialEncoder d.interpolant i)/denominator d i

theorem encoded_original (d : Data (K := K)) (checked : d.Checked)
    (Q : Fin 1024 → K) (image : Q 1023=0 ∧ d.b*Q 1022-d.c*Q 1021=0)
    (i : Fin 1048576) :
    exactInitialEncoder (d.original Q) i=
      denominator d i*exactInitialEncoder Q i+exactInitialEncoder d.interpolant i :=
  d.original_eval checked Q image (symbolX i) (symbolY i) (symbol_circle i)

def poleSymbols (d : Data (K := K)) : Finset (Fin 1048576) :=
  Finset.univ.filter fun i => denominator d i=0
def poleFibres (d : Data (K := K)) : Finset (Fin 262144) :=
  (poleSymbols d).image (parentIndex (n := 262144))

/-- The actual domain has injective stereographic parameters. A nonzero
degree-two chord numerator therefore has at most two stored zero symbols. -/
theorem poleSymbols_card (d : Data (K := K)) (checked : d.Checked) :
    (poleSymbols d).card≤2 := by
  let p := chordNumerator d.a d.b d.c
  have hp : p≠0 := chordNumerator_nonzero d.a d.b d.c (d.chord_nondegenerate checked)
  have hsubset : ((poleSymbols d).image parameter).val ⊆ p.roots := by
    intro t ht
    change t∈(poleSymbols d).image parameter at ht
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
    apply (Polynomial.mem_roots hp).mpr
    change p.eval (parameter i)=0
    rw [parameter_eq,chordNumerator_stereo d.a d.b d.c
      (symbolX i) (symbolY i) (symbol_circle i) (symbol_west i)]
    have hz : denominator d i=0 := (Finset.mem_filter.mp hi).2
    dsimp only [denominator] at hz
    rw [hz,mul_zero]
  calc
    (poleSymbols d).card=((poleSymbols d).image parameter).card :=
      (Finset.card_image_of_injective _ parameter_injective).symm
    _ ≤ p.natDegree := Polynomial.card_le_degree_of_subset_roots hsubset
    _ ≤ 2 := chordNumerator_degree d.a d.b d.c

theorem poleFibres_card (d : Data (K := K)) (checked : d.Checked) :
    (poleFibres d).card≤2 :=
  (Finset.card_image_le).trans (poleSymbols_card d checked)

theorem denominator_nonzero_outside_poles (d : Data (K := K))
    (i : Fin 262144) (outside : i∉poleFibres d) (slot : Fin 4) :
    denominator d (childIndex i slot)≠0 := by
  intro hz
  apply outside
  apply Finset.mem_image.mpr
  exact ⟨childIndex i slot,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩,
    parentIndex_childIndex i slot⟩

/-- On each non-pole symbol, quotient agreement and reconstructed original
agreement are equivalent, including their exact signs. -/
theorem symbol_agreement_iff (d : Data (K := K)) (checked : d.Checked)
    (Q : Fin 1024 → K) (image : Q 1023=0 ∧ d.b*Q 1022-d.c*Q 1021=0)
    (received : Fin 1048576 → K) (i : Fin 1048576) (nonzero : denominator d i≠0) :
    exactInitialEncoder Q i=virtual d received i ↔
      exactInitialEncoder (d.original Q) i=received i := by
  have h := quotient_eq_iff_reconstructed (received i) (exactInitialEncoder d.interpolant i)
    (denominator d i) (exactInitialEncoder Q i) nonzero
  constructor
  · intro agrees
    exact (encoded_original d checked Q image i).trans ((h.mp agrees.symm).symm)
  · intro agrees
    exact (h.mpr ((encoded_original d checked Q image i).symm.trans agrees).symm).symm

/-- Poles are retained as an explicit deterministic exceptional set, never
assigned a made-up tiny probability or removed from the received oracle. -/
theorem fibreBad_subset (d : Data (K := K)) (checked : d.Checked)
    (Q : Fin 1024 → K) (image : Q 1023=0 ∧ d.b*Q 1022-d.c*Q 1021=0)
    (received : Fin 1048576 → K) :
    fibreBad (m := 262144) (exactInitialEncoder (d.original Q)) received ⊆
      fibreBad (m := 262144) (exactInitialEncoder Q) (virtual d received) ∪ poleFibres d := by
  intro i hi
  by_cases pole : i∈poleFibres d
  · exact Finset.mem_union_right _ pole
  · apply Finset.mem_union_left
    obtain ⟨slot,wrong⟩ := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,slot,?_⟩
    intro same
    exact wrong ((symbol_agreement_iff d checked Q image received (childIndex i slot)
      (denominator_nonzero_outside_poles d i pole slot)).mp same)

theorem fibreBad_card (d : Data (K := K)) (checked : d.Checked)
    (Q : Fin 1024 → K) (image : Q 1023=0 ∧ d.b*Q 1022-d.c*Q 1021=0)
    (received : Fin 1048576 → K) :
    (fibreBad (m := 262144) (exactInitialEncoder (d.original Q)) received).card≤
      (fibreBad (m := 262144) (exactInitialEncoder Q) (virtual d received)).card+2 := by
  exact (Finset.card_le_card (fibreBad_subset d checked Q image received)).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left (poleFibres_card d checked) _))

/-- B=2324 is an analysis threshold, not a parameter/proof change. The
geometric 4B quotient loss plus at most two pole fibres remains below9301. -/
theorem geometric_2324_to_original (d : Data (K := K)) (checked : d.Checked)
    (Q : Fin 1024 → K) (image : Q 1023=0 ∧ d.b*Q 1022-d.c*Q 1021=0)
    (received : Fin 1048576 → K)
    (close : (fibreBad (m := 262144) (exactInitialEncoder Q) (virtual d received)).card≤4*2324) :
    (fibreBad (m := 262144) (exactInitialEncoder (d.original Q)) received).card≤9298 := by
  have bound := fibreBad_card d checked Q image received
  omega

#print axioms symbol_circle
#print axioms parameter_injective
#print axioms encoded_original
#print axioms poleSymbols_card
#print axioms poleFibres_card
#print axioms symbol_agreement_iff
#print axioms fibreBad_subset
#print axioms fibreBad_card
#print axioms geometric_2324_to_original
end
end AspisV8.SelectedQuotientOriginal
