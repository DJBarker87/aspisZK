import R1UnifiedCausalBound
import R1UnifiedSamplerLaw
import R1RhoSamplerBound
import R1QueryResidualBridge

/-! A conditional row-32 density adapter for the explicit rho residual set.
The decoder, challenge projection, and sampler equivalences remain supplied
inputs; this file proves no acceptance, extraction, or source correspondence. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedRhoDensity

open FS FS2 FS2.Duplex R0C.V3
open AspisCircleGroupOrder AspisR1.MatchingSupport
open AspisV8PairedCommitment AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound
open TranscriptView

variable {M Cv K E Pf : Type} {L : Nat}
  [Field K] [Fintype K] [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) E]

private theorem rho_cap_nonneg : 0 ≤ RhoSamplerBound.rhoCap := by
  unfold RhoSamplerBound.rhoCap
  apply mul_nonneg (by norm_num)
  apply div_nonneg
  · exact Nat.cast_nonneg _
  · exact Nat.cast_nonneg _

def rhoBad
    (iota : K →+* E) (rhoOf : Cv → K)
    (decoded : UnifiedSampler.Prefix M Cv L → Message M → Table (Addr L) State →
      Option (MatchingSupport.Data E × (Fin 22 → Fin 262144)))
    (P : UnifiedSampler.Prefix M Cv L) (m : Message M)
    (T : Table (Addr L) State) (ch : Challenge Cv) : Prop :=
  match P.rounds.length, m, ch.1, decoded P m T with
  | 32, .payload _, .ordinary rho, some (d, q) =>
      rhoOf rho ∈ QueryResidualBridge.rhoBad iota d q
  | _, _, _, _ => False

private theorem independentMean_zero {I A O : Type} [Fintype A] [Nonempty A]
    (q : Program I A O) :
    independentMean q (fun _ => (0 : ℚ)) = 0 := by
  induction q with
  | done _ => rfl
  | ask i k ih =>
      simp only [independentMean]
      rw [show (fun a => independentMean (k a) (fun _ => (0 : ℚ))) =
        fun _ => (0 : ℚ) from funext fun a => ih a]
      simp [mean_const]

theorem rho_row_density_bound (p : Params M Cv L) (hD : 5 ≤ p.D)
    (iota : K →+* E) (rhoOf : Cv → K)
    (decoded : UnifiedSampler.Prefix M Cv L → Message M → Table (Addr L) State →
      Option (MatchingSupport.Data E × (Fin 22 → Fin 262144)))
    (input : State ≃ Fin (2^256)) (output : Fin (P^4) ≃ K)
    (hsigma : ∀ s : State,
      rhoOf (p.σ 32 s) = output
        (R0C.ModuloCounting.reduce
          (by norm_num [AspisCircleGroupOrder.P]) (input s)))
    (T : Table (Addr L) State) (P : UnifiedSampler.Prefix M Cv L)
    (msg : M) (hround : P.rounds.length = 32) :
    independentMean (UnifiedSampler.samp p hD 32 P (.payload msg)).toProgram
      (fun w => indicator (rhoBad iota rhoOf decoded P (.payload msg) T w.2)) ≤
        RhoSamplerBound.rhoCap := by
  have hlaw := UnifiedSampler.unified_law p hD 32 P (.payload msg)
    (fun ch => indicator (rhoBad iota rhoOf decoded P (.payload msg) T ch))
    (by omega) (by simp [UnifiedSampler.messageValid])
  rw [hlaw]
  cases hd : decoded P (.payload msg) T with
  | none =>
      have hzero : ∀ b x,
          rhoBad iota rhoOf decoded P (.payload msg) T
            (TranscriptView.liftChallenge (p.σ 32 b, x)) = False := by
        intro b x
        simp [rhoBad, hround, hd, TranscriptView.liftChallenge]
      simp_rw [hzero, indicator_false, mean_const]
      exact rho_cap_nonneg
  | some dq =>
      rcases dq with ⟨d, q⟩
      have hform : ∀ b x,
          rhoBad iota rhoOf decoded P (.payload msg) T
            (TranscriptView.liftChallenge (p.σ 32 b, x)) =
          (rhoOf (p.σ 32 b) ∈ QueryResidualBridge.rhoBad iota d q) := by
        intro b x
        simp [rhoBad, hround, hd, TranscriptView.liftChallenge]
      simp_rw [hform, mean_const]
      have hmean : mean (fun b : State => indicator
          (rhoOf (p.σ 32 b) ∈ QueryResidualBridge.rhoBad iota d q)) =
          mean (fun a : State => indicator
            (output (R0C.ModuloCounting.reduce
              (by norm_num [AspisCircleGroupOrder.P]) (input a)) ∈
              QueryResidualBridge.rhoBad iota d q)) := by
        apply mean_congr
        intro a
        rw [hsigma a]
      rw [hmean]
      unfold RhoSamplerBound.rhoCap
      exact RhoSamplerBound.modulo_bad_mass
        (by norm_num [AspisCircleGroupOrder.P]) input output iota d q

theorem rho_density_bound (p : Params M Cv L) (hD : 5 ≤ p.D)
    (iota : K →+* E) (rhoOf : Cv → K)
    (decoded : UnifiedSampler.Prefix M Cv L → Message M → Table (Addr L) State →
      Option (MatchingSupport.Data E × (Fin 22 → Fin 262144)))
    (input : State ≃ Fin (2^256)) (output : Fin (P^4) ≃ K)
    (hsigma : ∀ s : State,
      rhoOf (p.σ 32 s) = output
        (R0C.ModuloCounting.reduce
          (by norm_num [AspisCircleGroupOrder.P]) (input s))) :
    ∀ (T : Table (Addr L) State) (i : Nat) (P : UnifiedSampler.Prefix M Cv L)
      (m : Message M), i < 33 → P.rounds.length = i →
      independentMean (UnifiedSampler.samp p hD i P m).toProgram
        (fun w => indicator (rhoBad iota rhoOf decoded P m T w.2)) ≤
          RhoSamplerBound.rhoCap := by
  intro T i P m hi hround
  by_cases hi32 : i = 32
  · subst i
    cases m with
    | initial c1 =>
        have hfalse : ∀ ch, rhoBad iota rhoOf decoded P (.initial c1) T ch = False := by
          intro ch
          simp [rhoBad]
        have hzero : (fun w : View (Addr L) State (Challenge Cv) =>
            indicator (rhoBad iota rhoOf decoded P (.initial c1) T w.2)) =
            fun _ => (0 : ℚ) := by
          funext w
          rw [hfalse]
          exact indicator_false
        rw [hzero, independentMean_zero]
        exact rho_cap_nonneg
    | payload msg =>
        have hlen : P.rounds.length = 32 := by omega
        rw [hlen]
        exact rho_row_density_bound p hD iota rhoOf decoded input output hsigma
          T P msg hlen
  · have hzero : (fun w : View (Addr L) State (Challenge Cv) =>
        indicator (rhoBad iota rhoOf decoded P m T w.2)) = fun _ => (0 : ℚ) := by
      funext w
      cases m with
      | initial c1 => simp [rhoBad, indicator_false]
      | payload msg =>
          simp [rhoBad, hround, hi32, indicator_false]
    rw [hzero, independentMean_zero]
    exact rho_cap_nonneg

theorem rho_first_hit_bound (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (iota : K →+* E) (rhoOf : Cv → K)
    (decoded : UnifiedSampler.Prefix M Cv L → Message M → Table (Addr L) State →
      Option (MatchingSupport.Data E × (Fin 22 → Fin 262144)))
    (input : State ≃ Fin (2^256)) (output : Fin (P^4) ≃ K)
    (hsigma : ∀ s : State,
      rhoOf (p.σ 32 s) = output
        (R0C.ModuloCounting.reduce
          (by norm_num [AspisCircleGroupOrder.P]) (input s)))
    (q : Program (Addr L) State (Pf × Bool)) (t : Table (Addr L) State)
    (N : Nat) (hN : FirstReadsBound q t N) :
    lazyMean q t (fun v =>
      indicator (hitsChain3 (UnifiedDecoder.decode p hD pub)
        (rhoBad iota rhoOf decoded) t v.1)) ≤
          (N : ℚ) * RhoSamplerBound.rhoCap := by
  exact UnifiedCausalBound.first_hit_bound p hD pub (rhoBad iota rhoOf decoded)
    RhoSamplerBound.rhoCap rho_cap_nonneg
    (rho_density_bound p hD iota rhoOf decoded input output hsigma) q t N hN

#print axioms rho_row_density_bound
#print axioms rho_density_bound
#print axioms rho_first_hit_bound

end AspisR1.UnifiedRhoDensity
end
