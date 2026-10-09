import R0.Chord
import R0.FunctionalWeights
import R0.ListsResponses
import R0.RootCounts

/-! R0 opening data over abstract committed words. All challenges and
prover messages are variables. No transcript, hash, or sampling is modeled. -/
set_option autoImplicit false
namespace AspisR0.Opening
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder AspisWide.FinalEncoder AspisWide.Agreement
open AspisV6Width29CorrelatedAgreement
open AspisR0.ListsResponses AspisR0.Chord AspisR0.ChordImage AspisR0.ChordGeometry
open AspisR0.RoundNormalization AspisR0.Fold AspisR0.RootCounts
open Polynomial
open scoped BigOperators
noncomputable section
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

structure Data (K : Type) [Field K] where
  W : Fin 29 → InitialWord K
  z0 : Point K
  z1 : Point K
  y : Fin 29 → Fin 2 → K
  points : Fin 3 → Fin 10 → K
  pointClaims : Fin 3 → Fin 29 → K
  inactive : Finset (Fin 1024)
  transport : Fin 1024 ≃ Fin 1024
  extraWeight : InitialMessage K
  extraClaims : Fin 29 → K

/-- The Boolean multilinear equality weights, indexed by the ten bits. -/
def eqWeight (p : Fin 10 → K) : InitialMessage K := fun r =>
  ∏ b : Fin 10, if r.val / 2^b.val % 2 = 0 then 1-p b else p b

def indicator (I : Finset (Fin 1024)) : InitialMessage K := fun r => if r ∈ I then 1 else 0

/-- A row-space weight reindexed into coefficient space. -/
def coeffWeight (π : Fin 1024 ≃ Fin 1024) (w : InitialMessage K) : InitialMessage K :=
  fun j => w (π.symm j)

theorem coeffWeight_add (π : Fin 1024 ≃ Fin 1024) (w v : InitialMessage K) :
    coeffWeight π (w + v) = coeffWeight π w + coeffWeight π v := rfl

theorem coeffWeight_smul (π : Fin 1024 ≃ Fin 1024) (a : K) (w : InitialMessage K) :
    coeffWeight π (a • w) = a • coeffWeight π w := rfl

theorem coeffWeight_sum {ι : Type*} (π : Fin 1024 ≃ Fin 1024)
    (s : Finset ι) (w : ι → InitialMessage K) :
    coeffWeight π (∑ i ∈ s, w i) = ∑ i ∈ s, coeffWeight π (w i) := by
  funext j
  simp only [coeffWeight, Finset.sum_apply]

theorem dot_coeffWeight_left (π : Fin 1024 ≃ Fin 1024) (w m : InitialMessage K) :
    dot (coeffWeight π w) m = dot w (fun r => m (π r)) := by
  simpa only [dot, coeffWeight, Equiv.symm_apply_apply] using
    (Equiv.sum_comp π (fun j => w (π.symm j) * m j)).symm

theorem dot_coeffWeight_indicator (π : Fin 1024 ≃ Fin 1024)
    (I : Finset (Fin 1024)) (m : InitialMessage K) :
    dot (coeffWeight π (indicator I)) m = ∑ r ∈ I, m (π r) := by
  rw [dot_coeffWeight_left]
  simp only [indicator, dot, ite_mul, one_mul, zero_mul, ← Finset.sum_filter,
    Finset.filter_mem_eq_inter, Finset.univ_inter]

def interpolants (D : Data K) : Fin 29 → InitialMessage K := fun l => interpolant D.z0 D.z1 (D.y l)
def virtual (D : Data K) : Fin 29 → InitialWord K := fun l i =>
  (D.W l i-exactInitialEncoder (interpolants D l) i)/L D.z0 D.z1 i

def batch (D : Data K) (gamma : K) : InitialWord K := width29CurveValue (virtual D) gamma

def imageFunctional (D : Data K) (i : Fin 2) : InitialMessage K →ₗ[K] K :=
  if i = 0 then e1 else e2 (secantB D.z0 D.z1) (secantC D.z0 D.z1)

def discrepancy (D : Data K) (t : Fin 29 → InitialMessage K) (j : Fin 3) (l : Fin 29) : K :=
  D.pointClaims j l-dot (coeffWeight D.transport (eqWeight (D.points j))) (t l)
def pointDefect (D : Data K) (gamma : K) (t : Fin 29 → InitialMessage K) (j : Fin 3) : K :=
  width29Batch (discrepancy D t j) gamma

def extraDiscrepancy (D : Data K) (t : Fin 29 → InitialMessage K) (l : Fin 29) : K :=
  D.extraClaims l-dot D.extraWeight (t l)

def extraDefect (D : Data K) (gamma : K) (t : Fin 29 → InitialMessage K) : K :=
  width29Batch (extraDiscrepancy D t) gamma

def inactiveDefect (D : Data K) (gamma v : K) (t : Fin 29 → InitialMessage K) : K :=
  v-dot (coeffWeight D.transport (indicator D.inactive)) (exactInitialMessageCurve t gamma)

def weights (D : Data K) (kappa : K) : InitialMessage K :=
  coeffWeight D.transport
    ((∑ j : Fin 3, kappa^(j.val+1) • eqWeight (D.points j))+indicator D.inactive) +
    kappa^4 • D.extraWeight

def claim (D : Data K) (gamma v kappa : K) : K :=
  (∑ j : Fin 3, kappa^(j.val+1)*width29Batch (D.pointClaims j) gamma)+v +
    kappa^4 * width29Batch D.extraClaims gamma

def claimPrime (D : Data K) (gamma v kappa : K) : K :=
  claim D gamma v kappa-dot (weights D kappa) (exactInitialMessageCurve (interpolants D) gamma)

def qWeights (D : Data K) (kappa : K) : InitialMessage K :=
  quotientWeights (secantA D.z0 D.z1) (secantB D.z0 D.z1) (secantC D.z0 D.z1) (weights D kappa)

def totalWeights (D : Data K) (kappa tau : K) : InitialMessage K :=
  qWeights D kappa+tau • FunctionalWeights.row (imageFunctional D 0)+
    tau^2 • FunctionalWeights.row (imageFunctional D 1)

/-- B2 and B3 are subsets of the protocol's nonzero gamma challenge space. -/
def B2 (D : Data K) : Finset K := by
  classical
  exact (LambdaR (virtual D)).biUnion fun t => Finset.univ.biUnion fun i : Fin 2 =>
    if (fun l => imageFunctional D i (t l)) = 0 then ∅
    else width29NonzeroCollisionSet (fun l => imageFunctional D i (t l))

def B3 (D : Data K) : Finset K := by
  classical
  exact (Lambda D.W).biUnion fun t =>
    (Finset.univ.biUnion fun j : Fin 3 =>
      if discrepancy D t j = 0 then ∅ else width29NonzeroCollisionSet (discrepancy D t j)) ∪
    (if extraDiscrepancy D t = 0 then ∅ else width29NonzeroCollisionSet (extraDiscrepancy D t))

def pointPolynomial (D : Data K) (gamma v : K) (t : Fin 29 → InitialMessage K) : K[X] :=
  C (inactiveDefect D gamma v t)+(∑ j : Fin 3, monomial (j.val+1) (pointDefect D gamma t j)) +
    monomial 4 (extraDefect D gamma t)

def B4 (D : Data K) (gamma v : K) : Finset K := by
  classical
  exact Finset.univ.filter fun kappa => ∃ t ∈ Lambda D.W,
    (pointDefect D gamma t ≠ 0 ∨ extraDefect D gamma t ≠ 0) ∧
      (pointPolynomial D gamma v t).eval kappa = 0

def imagePolynomial (D : Data K) (gamma v kappa : K) (q : InitialMessage K) : K[X] :=
  C (dot (qWeights D kappa) q-claimPrime D gamma v kappa)+
    monomial 1 (imageFunctional D 0 q)+monomial 2 (imageFunctional D 1 q)

def B5 (D : Data K) (gamma v kappa : K) : Finset K :=
  (Close (batch D gamma)).biUnion fun q => badRoots (imagePolynomial D gamma v kappa q)

def B7 (D : Data K) (gamma kappa tau : K) (P : K[X]) : Finset K :=
  (Close (batch D gamma)).biUnion fun q => badRoots (P-roundPolynomial q (totalWeights D kappa tau))

def matchingFibres (D : Data K) (gamma alpha : K) (F : FinalMessage K) : Finset (Fin 262144) :=
  Finset.univ.filter fun u => exactFinalEncoder F u = foldWord alpha (batch D gamma) u

def V1 (D : Data K) (gamma alpha : K) (F : FinalMessage K) (S : Finset (Fin 262144)) : Prop :=
  ∀ u ∈ S, exactFinalEncoder F u = foldWord alpha (batch D gamma) u

def V2 (D : Data K) (kappa tau alpha : K) (P : K[X]) (F : FinalMessage K) : Prop :=
  P.eval alpha = quarter*dot F (citedDualFold alpha (totalWeights D kappa tau))

/-- Semantic and authentication checks are abstract Boolean propositions here. -/
def Accept (D : Data K) (gamma v kappa tau alpha : K) (P : K[X])
    (F : FinalMessage K) (S : Finset (Fin 262144)) (semantic authentic : Prop) : Prop :=
  semantic ∧ authentic ∧ P.natDegree ≤ 6 ∧
  P.coeff 0+P.coeff 4 = quarter*claimPrime D gamma v kappa ∧
  V1 D gamma alpha F S ∧ V2 D kappa tau alpha P F

end
end AspisR0.Opening
