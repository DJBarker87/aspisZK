import AspisRowDensitySampler
import AspisRows40Final

/-! Aspis one-transaction verifier: the row-density theorems of rows 33 to 39
carried to the decoded start of the final component.

`Final.decoded_bound` (copy of R1's `JointUnifiedBound.decoded_bound`) turns
a fixed-prefix bound on row n's sampler into a bound on the decoded start's
background law. The fixed-prefix bounds are the row-densities agent's
`Sampler.combining_unified_density` (row 33, bad set of size at most 1) and
`Sampler.round_unified_density` (rows 34 to 39, bad sets of size at most 2),
with the bad set read from the completed prefix and the row's message. The
bad set (`read`, `S`) is a parameter: the classifier events come from the
acceptance-link agent. `hσ` holds for R1's parameters on every row from 32
on (`AspisRows40.Protocol.final_sigma_rho`). -/
set_option autoImplicit false
noncomputable section
namespace AspisRows40.FinalDensity
open FS FS2 FS2.Duplex R0C.V3
open AspisR1
open AspisV8R19.SourceDuplexStep AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.AdaptiveFirstReadLaw
open AspisRowDensity.QM31 AspisRowDensity.Sampler

/-- The decoded start of row 33 (combining challenge). -/
theorem combining_decoded {M : Type} {L : Nat} {X : Type}
    (read : UnifiedSampler.Prefix M E L × TranscriptView.Message M → Option X)
    (S : X → Finset K) (hS : ∀ x, (S x).card ≤ 1)
    (p : FS2.Duplex.Params M E L) (hD : 5 ≤ p.D)
    (hσ : ∀ s, SelectedChallengeMap.rhoOf (p.σ 33 s) = R0P.SemSource.qm31Sample s)
    (pub : UnifiedSampler.Public L) (c : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State State) (pend : List (Addr L × Option State))
    (g : State → List State → JointTranscriptView.Output M E L)
    (hd : Final.decode p pub 33 c T = some (own, pend, g)) :
    blaw g (fun out => indicator (ordEvent (setBad read S (out.1, out.2.1)) out.2.2)) own pend ≤
      capLambda :=
  Final.decoded_bound p hD pub 33 le_rfl c T own pend g hd _ _
    (fun ctx _ as _ => combining_unified_density read S hS p hD 33 _ _ (by decide)
      (Final.messageValid_final 33 le_rfl _) hσ)

/-- The decoded start of a round challenge (rows 34 to 39). -/
theorem round_decoded {M : Type} {L : Nat} {X : Type}
    (read : UnifiedSampler.Prefix M E L × TranscriptView.Message M → Option X)
    (S : X → Finset K) (hS : ∀ x, (S x).card ≤ 2)
    (p : FS2.Duplex.Params M E L) (hD : 5 ≤ p.D) (n : Nat) (hlo : 34 ≤ n)
    (hσ : ∀ s, SelectedChallengeMap.rhoOf (p.σ n s) = R0P.SemSource.qm31Sample s)
    (pub : UnifiedSampler.Public L) (c : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State State) (pend : List (Addr L × Option State))
    (g : State → List State → JointTranscriptView.Output M E L)
    (hd : Final.decode p pub n c T = some (own, pend, g)) :
    blaw g (fun out => indicator (ordEvent (setBad read S (out.1, out.2.1)) out.2.2)) own pend ≤
      capRound :=
  Final.decoded_bound p hD pub n (by omega) c T own pend g hd _ _
    (fun ctx _ as _ => round_unified_density read S hS p hD n _ _ (by omega)
      (Final.messageValid_final n (by omega) _) hσ)

/-- Unified-dispatcher forms. -/
theorem combining_component {M : Type} {L : Nat} {X : Type}
    (read : UnifiedSampler.Prefix M E L × TranscriptView.Message M → Option X)
    (S : X → Finset K) (hS : ∀ x, (S x).card ≤ 1)
    (p : FS2.Duplex.Params M E L) (hD : 5 ≤ p.D)
    (hσ : ∀ s, SelectedChallengeMap.rhoOf (p.σ 33 s) = R0P.SemSource.qm31Sample s)
    (pub : UnifiedSampler.Public L) (c : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State (List State)) (pend : List (Addr L × Option State))
    (g : List State → List State → JointTranscriptView.Output M E L)
    (hd : Final.component p pub 33 c T = some (own, pend, g)) :
    blaw g (fun out => indicator (ordEvent (setBad read S (out.1, out.2.1)) out.2.2)) own pend ≤
      capLambda :=
  Final.component_bound p hD pub 33 le_rfl c T own pend g hd _ _
    (fun ctx _ as _ => combining_unified_density read S hS p hD 33 _ _ (by decide)
      (Final.messageValid_final 33 le_rfl _) hσ)

theorem round_component {M : Type} {L : Nat} {X : Type}
    (read : UnifiedSampler.Prefix M E L × TranscriptView.Message M → Option X)
    (S : X → Finset K) (hS : ∀ x, (S x).card ≤ 2)
    (p : FS2.Duplex.Params M E L) (hD : 5 ≤ p.D) (n : Nat) (hlo : 34 ≤ n)
    (hσ : ∀ s, SelectedChallengeMap.rhoOf (p.σ n s) = R0P.SemSource.qm31Sample s)
    (pub : UnifiedSampler.Public L) (c : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State (List State)) (pend : List (Addr L × Option State))
    (g : List State → List State → JointTranscriptView.Output M E L)
    (hd : Final.component p pub n c T = some (own, pend, g)) :
    blaw g (fun out => indicator (ordEvent (setBad read S (out.1, out.2.1)) out.2.2)) own pend ≤
      capRound :=
  Final.component_bound p hD pub n (by omega) c T own pend g hd _ _
    (fun ctx _ as _ => round_unified_density read S hS p hD n _ _ (by omega)
      (Final.messageValid_final n (by omega) _) hσ)

#print axioms combining_decoded
#print axioms round_decoded
#print axioms combining_component
#print axioms round_component

end AspisRows40.FinalDensity
end
