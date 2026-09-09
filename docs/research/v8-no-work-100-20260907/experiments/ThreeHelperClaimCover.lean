import ThreeHelperSelected
import SelectedQuotientOriginal
import GammaEligibility

/-! The three-helper cover is connected to the actual quotient/reconstruction
map, retaining the optional early-C1 and sparse-gamma branches. The dense
tuple is constructed before all OOD data, claimed values and relation strategy.
This is deterministic geometric coverage, not acceptance or extraction. -/
set_option autoImplicit false
set_option maxRecDepth 200
set_option maxHeartbeats 50000
namespace AspisV8.ThreeHelperClaimCover
open Finset
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.NearGammaSelectedC1 AspisV8.NearGammaFibreBridge
open AspisV8.FixedC1HelperReduction AspisV8.ThreeHelperSelected
open AspisV8.NearGammaSelectedCoefficients AspisV8.PartialFoldRecovery
open AspisPool.V7C1ConcreteProjectionBinding
noncomputable section
local instance decision (p : Prop) : Decidable p := Classical.propDecidable p
local instance : Fintype (Fin 262144) := AspisV8.EarlyC1Specialization.explicit_instance
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

def join (p : C1Messages) (h : Fin 3 → Message) : Fin 29 → Message :=
  fun lane => if small : lane.val<26 then p ⟨lane.val,small⟩
    else h ⟨lane.val-26,by omega⟩

theorem join_left (p : C1Messages) (h : Fin 3 → Message) (lane : Fin 26) :
    join p h (Fin.castAdd 3 lane)=p lane := by
  simp only [join,Fin.val_castAdd,dif_pos lane.isLt]

theorem join_right (p : C1Messages) (h : Fin 3 → Message) (lane : Fin 3) :
    join p h (Fin.natAdd 26 lane)=h lane := by
  have notLeft : ¬26+lane.val<26 := by omega
  simp only [join,Fin.val_natAdd,dif_neg notLeft,Nat.add_sub_cancel_left]

theorem join_projection (p : C1Messages) (h : Fin 3 → Message) :
    c1Projection (join p h)=p := by
  funext lane
  exact join_left p h lane

/-- ClaimTransport was compiled with Fin.fintype; the selected scalar helper
has an imported Simplex-category enumeration of the same carrier. Transport
their identical finite set symbolically instead of unfolding either sum. -/
private theorem same_whole_enumeration :
    @Finset.univ (Fin 29)
      (SimplexCategory.instFintypeToTypeOrderHomFinHAddNatLenOfNat (SimplexCategory.mk 28))=
      @Finset.univ (Fin 29) (Fin.fintype 29) :=
  congrArg (fun enumeration : Fintype (Fin 29) => @Finset.univ (Fin 29) enumeration)
    (Subsingleton.elim _ _)

/-- All 29 powers are retained; only their deterministic evaluation is split. -/
theorem batch_join (p : C1Messages) (h : Fin 3 → Message) (gamma : K) :
    ClaimTransport.batch gamma (join p h)=c1Batch p gamma+gamma^26 • helperBatch h gamma := by
  funext index
  simp only [ClaimTransport.batch,c1Batch,helperBatch,Finset.sum_apply,
    Pi.smul_apply,smul_eq_mul,Pi.add_apply]
  have split := split_sum (fun lane => join p h lane index) gamma
  simp only [lowClaims,helperClaims,join_left,join_right] at split
  rw [same_whole_enumeration] at split
  dsimp only [AspisV8.NearGammaSelectedC1.K] at split
  -- Only the final comparison traverses the expanded field-parameter type.
  -- No finite enumeration or field arithmetic is unfolded by this proof.
  set_option maxRecDepth 400 in exact split

def ownSupport (received : C1Received) (p : C1Messages) : Finset (Fin 262144) :=
  support fibreEncode (receivedFibres received) p

def goodGammas (received : C1Received) (p : C1Messages) (c2 : C2Received)
    (G : Finset K) : Finset K :=
  goodOn c2 (ownSupport received p) 61338 G

theorem good_subset (received : C1Received) (p : C1Messages) (c2 : C2Received)
    (G : Finset K) : goodGammas received p c2 G⊆G :=
  GammaEligibility.good_subset code (ownSupport received p) (helperFibres c2) 61338 G

theorem ownSupport_same (received : C1Received) (p : C1Messages)
    (f : Fin 262144) (member : f∈ownSupport received p) (s : Fin 4) (lane : Fin 26) :
    received lane (fibreEmbed (f,s))=exactInitialEncoder (p lane) (fibreEmbed (f,s)) := by
  letI : DecidablePred (fun x : Fin 262144 => ∀ column : Fin 26,
      receivedFibres received column x=fibreEncode (p column) x) :=
    fun _ => Classical.propDecidable _
  exact congrFun ((mem_filter.mp member).2 lane) s

/-- Restricting to the actual C1 own support cannot add bad fibres. The
orientation and stored-index mapping are the already proved source ones. -/
theorem rawBad_card_le_full (received : C1Received) (c2 : C2Received)
    (gamma : K) (message : Message) (S : Finset (Fin 262144)) :
    (rawBad received c2 gamma message S).card≤
      (fibreBad (m:=262144) (exactInitialEncoder message) (rawBatch received c2 gamma)).card := by
  rw [fibreBad_raw_eq]
  apply Finset.card_le_card
  intro f member
  exact mem_filter.mpr ⟨mem_univ f,(mem_filter.mp member).2⟩

/-- Four-fold geometric loss plus at most two actual chord-pole fibres.
There is no global nonzero-denominator or received-polynomial premise. -/
theorem close_original_on_support (received : C1Received) (c2 : C2Received)
    (gamma : K) (S : Finset (Fin 262144)) (d : OODInterpolant.Data (K:=K))
    (checked : d.Checked) (Q : Message)
    (image : Q 1023=0 ∧ d.b*Q 1022-d.c*Q 1021=0)
    (close : (fibreBad (m:=262144) (exactInitialEncoder Q)
      (SelectedQuotientOriginal.virtual d (rawBatch received c2 gamma))).card≤4*15334) :
    (rawBad received c2 gamma (d.original Q) S).card≤61338 := by
  have restricted := rawBad_card_le_full received c2 gamma (d.original Q) S
  have poles := SelectedQuotientOriginal.fibreBad_card d checked Q image
    (rawBatch received c2 gamma)
  omega

/-- An image-valid close quotient is included in the same pre-gamma Good
set, even in its sparse branch. This does not assert that such a quotient
exists or that acceptance implies closeness. -/
theorem good_of_close_image (received : C1Received) (p : C1Messages) (c2 : C2Received)
    (G : Finset K) (gamma : K) (member : gamma∈G) (nonzero : gamma≠0)
    (d : OODInterpolant.Data (K:=K)) (checked : d.Checked) (Q : Message)
    (image : Q 1023=0 ∧ d.b*Q 1022-d.c*Q 1021=0)
    (close : (fibreBad (m:=262144) (exactInitialEncoder Q)
      (SelectedQuotientOriginal.virtual d (rawBatch received c2 gamma))).card≤4*15334) :
    gamma∈goodGammas received p c2 G := by
  have near := raw_near_helper received p c2 gamma nonzero (d.original Q)
    (ownSupport received p) 61338 (ownSupport_same received p)
    (close_original_on_support received c2 gamma (ownSupport received p) d checked Q image close)
  exact GammaEligibility.good_mem code (ownSupport received p) (helperFibres c2)
    61338 G gamma member (fibreEncode (normalized p gamma (d.original Q))) near

/-- The exact tuple precedes data, gamma, candidate, claims and strategy.
Its C1 projection is the unchanged early optional object. The sparse branch
is not erased, and no helper agreement outside the C1 own support is asserted. -/
theorem quotient_cover_dichotomy (received : C1Received) (p : C1Messages) (c2 : C2Received)
    (G : Finset K) (nonzero : ∀ gamma∈G, gamma≠0)
    (found : earlyC1 received=some p) :
    (goodGammas received p c2 G).card<3 ∨
      ∃ P : Fin 29 → Message, c1Projection P=p ∧
        ∀ d : OODInterpolant.Data (K:=K), d.Checked →
        ∀ gamma∈G, ∀ Q : Message,
          Q 1023=0 ∧ d.b*Q 1022-d.c*Q 1021=0 →
          (fibreBad (m:=262144) (exactInitialEncoder Q)
            (SelectedQuotientOriginal.virtual d (rawBatch received c2 gamma))).card≤4*15334 →
          d.original Q=ClaimTransport.batch gamma P := by
  rcases early_cover received p c2 G nonzero found with sparse | ⟨h,covered⟩
  · exact Or.inl sparse
  · refine Or.inr ⟨join p h,join_projection p h,?_⟩
    intro d checked gamma member Q image close
    have raw := close_original_on_support received c2 gamma (ownSupport received p)
      d checked Q image close
    exact (covered gamma member (d.original Q) raw).trans (batch_join p h gamma).symm

#print axioms join_left
#print axioms join_right
#print axioms join_projection
#print axioms batch_join
#print axioms good_subset
#print axioms ownSupport_same
#print axioms rawBad_card_le_full
#print axioms close_original_on_support
#print axioms good_of_close_image
#print axioms quotient_cover_dichotomy
end
end AspisV8.ThreeHelperClaimCover
