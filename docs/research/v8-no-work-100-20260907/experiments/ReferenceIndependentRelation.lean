import RepresentedImageGame

/-! The quotient reference is an analysis object. Replacing it does not
change any executed weight, claim, received slot, compact response, or
terminal acceptance. The supported event itself is held fixed: this does
not say that two different coverage predicates have the same probability. -/
set_option autoImplicit false
namespace AspisV8.ReferenceIndependentRelation
open Finset
open AspisV8.JointImageGame AspisV8.OptimizedRelationRefinement
open AspisV8.FirstImageDiscrepancy AspisV8.PostQueryFunctional
open AspisV8.CausalOrderedRelation AspisV8.ShiftedRowPrefix
open AspisV8.RepresentedImageGame
variable {K : Type*} [Field K] [DecidableEq K] [NeZero (2 : K)]

def replacePrefix (p : Prefix (K := K)) (Q : Fin 1024 → K) : Prefix (K := K) :=
  { p with referenceQ := Q }

def replaceBefore (p : Before (K := K)) (Q : Fin 1024 → K) : Before (K := K) :=
  { p with referenceQ := Q }

def replaceRows (r : Rows (K := K)) (Q : Fin 1024 → K) : Rows (K := K) :=
  { r with referenceQ := Q }

/-- Changing an arbitrary reference cannot preserve an old small-support
certificate. Its analysis support is explicitly widened to D. Received
values and coordinates are unchanged. The selected source uses D D already. -/
def replaceOracle {D B : Finset K} {Q0 : Fin 1024 → K}
    (o : FixedOracle D B Q0) (Q : Fin 1024 → K) : FixedOracle D D Q :=
  arbitraryOracle D Q o.x o.y o.slots o.x_nonzero o.y_nonzero o.coordinate

theorem replaceOracle_folded {D B : Finset K} {Q0 : Fin 1024 → K}
    (o : FixedOracle D B Q0) (Q : Fin 1024 → K) (alpha : K) :
    (replaceOracle o Q).folded alpha=o.folded alpha := rfl

theorem replacePrefix_imageWeight (p : Prefix (K := K)) (Q : Fin 1024 → K) :
    (replacePrefix p Q).imageWeight=p.imageWeight := rfl
theorem replacePrefix_foldWeight (p : Prefix (K := K)) (Q : Fin 1024 → K) :
    (replacePrefix p Q).foldWeight=p.foldWeight := rfl
theorem replacePrefix_carried (p : Prefix (K := K)) (Q : Fin 1024 → K) :
    (replacePrefix p Q).carried=p.carried := rfl
theorem replacePrefix_prior (p : Prefix (K := K)) (Q : Fin 1024 → K)
    (final : Fin 256 → K) : (replacePrefix p Q).prior final=p.prior final := rfl

theorem replacePrefix_postWeights {q : ℕ} (p : Prefix (K := K)) (Q : Fin 1024 → K)
    (points : Fin q → K) (rho : K) :
    postWeights (replacePrefix p Q) points rho=postWeights p points rho := rfl
theorem replacePrefix_postClaim {q : ℕ} (p : Prefix (K := K)) (Q : Fin 1024 → K)
    (points : Fin q → K) (received : K → K) (rho : K) :
    postClaim (replacePrefix p Q) points received rho=postClaim p points received rho := rfl

/-- Only the type index is transported. This lemma does not replace a game
by an arbitrary acceptance predicate or assume equal transcript outcomes. -/
theorem rounds_probability_transport {n : ℕ} {c d : K} (h : c=d)
    (g : Rounds n c) (A : Finset K) : (h ▸ g).prob A=g.prob A := by
  cases h
  rfl

/-- Erase the proved discrepancy equality used solely to index Rounds. The
right side is the game generated directly from executed weights and claim. -/
theorem tail_probability {q : ℕ} (p : Prefix (K := K)) (hq : p.quarter*4=1)
    (final : Fin 256 → K) (points : Fin q → K) (received : K → K) (rho : K)
    (raw : RawRounds (K := K) 3 256) (A : Finset K) :
    (tail p hq final points received rho raw).prob A=
      (raw.toGame p.quarter hq (postWeights p points rho) final
        (postClaim p points received rho)).prob A :=
  rounds_probability_transport (post_discrepancy p final points received rho) _ A

theorem replacePrefix_tail_probability {q : ℕ}
    (p : Prefix (K := K)) (Q : Fin 1024 → K) (hq : p.quarter*4=1)
    (final : Fin 256 → K) (points : Fin q → K) (received : K → K) (rho : K)
    (raw : RawRounds (K := K) 3 256) (A : Finset K) :
    (tail (replacePrefix p Q) hq final points received rho raw).prob A=
      (tail p hq final points received rho raw).prob A := by
  rw [tail_probability, tail_probability]
  rfl

theorem replaceRows_before (rows : Rows (K := K)) (Q : Fin 1024 → K) (kappa : K) :
    (replaceRows rows Q).before kappa=replaceBefore (rows.before kappa) Q := rfl

theorem replaceBefore_atFold {D : Finset K} {q : ℕ}
    (pre : Before (K := K)) (Q : Fin 1024 → K) (s : Strategy D q) (tau alpha : K) :
    atFold (replaceBefore pre Q) s tau alpha=replacePrefix (atFold pre s tau alpha) Q := rfl

/-- Actual compact suffix acceptance, including rejected challenge-list
lengths, is literally invariant. The strategy and actual received word are
the same; only the analysis quotient and its support bookkeeping change. -/
theorem accepts_iff {D B : Finset K} {q : ℕ}
    (pre : Before (K := K)) (Q : Fin 1024 → K)
    (o : FixedOracle D B pre.referenceQ) (s : Strategy D q)
    (tau alpha : K) (queries : OrderedQueryGame.Schedule D q) (rho : K)
    (later : List K) :
    accepts (replaceBefore pre Q) (replaceOracle o Q) s tau alpha queries rho later ↔
      accepts pre o s tau alpha queries rho later := Iff.rfl

theorem after_probability {D B : Finset K} {q : ℕ}
    (pre : Before (K := K)) (Q : Fin 1024 → K) (hq : pre.quarter*4=1)
    (o : FixedOracle D B pre.referenceQ) (s : Strategy D q)
    (tau alpha : K) (A G : Finset K) :
    (after (replaceBefore pre Q) hq (replaceOracle o Q) s tau alpha).prob A G=
      (after pre hq o s tau alpha).prob A G := by
  unfold OrderedQueryGame.After.prob
  congr 1

theorem supported_probability {D B : Finset K} {q : ℕ}
    (pre : Before (K := K)) (Q : Fin 1024 → K) (hq : pre.quarter*4=1)
    (o : FixedOracle D B pre.referenceQ) (s : Strategy D q)
    (support : K → K → Prop) (A G : Finset K) :
    supportedProbability (replaceBefore pre Q) hq (replaceOracle o Q) s support A G=
      supportedProbability pre hq o s support A G := by
  classical
  unfold supportedProbability
  apply congrArg (avg G)
  funext tau
  apply congrArg (avg A)
  funext alpha
  split_ifs
  · exact after_probability pre Q hq o s tau alpha A G
  · rfl

theorem rows_accepts_iff {D B : Finset K} {q : ℕ}
    (rows : Rows (K := K)) (Q : Fin 1024 → K)
    (o : FixedOracle D B rows.referenceQ) (strategy : K → Strategy D q)
    (kappa tau alpha : K) (queries : OrderedQueryGame.Schedule D q) (rho : K)
    (later : List K) :
    accepts ((replaceRows rows Q).before kappa) (replaceOracle o Q)
      (strategy kappa) tau alpha queries rho later ↔
    accepts (rows.before kappa) o (strategy kappa) tau alpha queries rho later :=
  accepts_iff (rows.before kappa) Q o (strategy kappa) tau alpha queries rho later

theorem supported_rows_probability {D B : Finset K} {q : ℕ}
    (rows : Rows (K := K)) (Q : Fin 1024 → K) (hq : rows.quarter*4=1)
    (o : FixedOracle D B rows.referenceQ) (strategy : K → Strategy D q)
    (support : K → K → K → Prop) (A G : Finset K) :
    supportedRowsProbability (replaceRows rows Q) hq (replaceOracle o Q)
      strategy support A G=supportedRowsProbability rows hq o strategy support A G := by
  unfold supportedRowsProbability
  apply congrArg (avg G)
  funext kappa
  exact supported_probability (rows.before kappa) Q hq o
    (strategy kappa) (support kappa) A G

#print axioms replaceOracle_folded
#print axioms replacePrefix_postWeights
#print axioms replacePrefix_postClaim
#print axioms tail_probability
#print axioms replacePrefix_tail_probability
#print axioms replaceRows_before
#print axioms accepts_iff
#print axioms after_probability
#print axioms supported_probability
#print axioms rows_accepts_iff
#print axioms supported_rows_probability
end AspisV8.ReferenceIndependentRelation
