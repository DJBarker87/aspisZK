import AcceptedAdaptiveFiatShamir
import R1GenericNoHit

/-! The existing membership reduction with recovery required only on
accepting executions. The specification choice extractor expresses absence
of a relation witness; efficient knowledge extraction remains separate. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.AcceptedAdaptiveMembershipSoundness

open FS FS2 R0C.V3 AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.OracleFiniteSupport

variable {X M C W Pf I A Y : Type} [DecidableEq I] [Inhabited A] [Fintype A]

theorem extractFails_iff_no_witness
    (pr : FS2.Protocol X M C W Pf I A) (relation : X → W → Prop)
    (hextract : ∀ x T, pr.extract x T = GenericNoHit.chooseWitness relation x)
    (v : View I A ((X × Pf) × Bool)) :
    AcceptedAdaptiveFiatShamir.extractFails pr v ↔
      ¬ ∃ w, relation v.2.1.1 w := by
  unfold AcceptedAdaptiveFiatShamir.extractFails FS2.extractFails
  split <;> rw [hextract, GenericNoHit.chooseWitness_eq_none_iff]

/-- The attacker selects the statement and proof together after its oracle
queries. Acceptance of a statement outside the relation has the same bound,
with no count or finiteness assumption on the statement space. All concrete
source, decoder, density and collision obligations remain explicit. -/
theorem membership_bound_outside
    (pr : FS2.Protocol X M C W Pf I A)
    (rb : RoundByRound' X M C I A) (dec : Dec X M C I A Y)
    (relation : X → W → Prop)
    (hextract : ∀ x T, pr.extract x T = GenericNoHit.chooseWitness relation x)
    (P : Program I A (X × Pf)) (V : X → Pf → Program I A Bool)
    (κ : Nat → ℚ) (Qtot : Nat)
    (hD1 : FS2.D1 pr rb) (hCD : ChainDensity3 pr rb dec)
    (hreads : ChainsRead pr) (hV : ReadsChains pr V)
    (inj : AcceptedAdaptiveFiatShamir.LazyInj pr dec P V κ Qtot)
    (hD3 : AcceptedAdaptiveFiatShamir.D3Outside pr rb P V inj.Coll)
    (hQ : ∀ H : I → A,
      distinctFirstReads (eval H (AcceptedAdaptiveFiatShamir.experiment P V)) ≤ Qtot) :
    lazyMean (AcceptedAdaptiveFiatShamir.experiment P V) emptyTable
      (fun v => indicator (accepts v ∧ ¬ ∃ w, relation v.2.1.1 w)) ≤
      (Qtot : ℚ) * maxErr rb.ε pr.r + κ Qtot := by
  have hbound := AcceptedAdaptiveFiatShamir.soundness_bound_outside
    pr rb dec P V κ Qtot hD1 hCD hreads hV inj hD3 hQ
  simpa only [extractFails_iff_no_witness pr relation hextract] using hbound

#print axioms extractFails_iff_no_witness
#print axioms membership_bound_outside
end AspisR1.AcceptedAdaptiveMembershipSoundness
end
