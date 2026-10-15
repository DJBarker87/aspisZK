import R1UnifiedCausalBound
import R1UnifiedSamplerLaw
import R1QueryBackgroundLaw
import R0C.V3.Q22Law

/-! A conditional row-31 density bound for a table-decoded finite query set.
The decoded set is fixed by the prefix, message, and table before the query
sampler runs. This file does not establish a transcript decoder or acceptance
implication. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedQueryDensity

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound
open TranscriptView

variable {M Cv : Type} {L : Nat} {Pf : Type}

def queryBad
    (decoded : UnifiedSampler.Prefix M Cv L → Message M → Table (Addr L) State →
      Option (Finset (Fin 262144)))
    (P : UnifiedSampler.Prefix M Cv L) (m : Message M)
    (T : Table (Addr L) State) (ch : TranscriptView.Challenge Cv) : Prop :=
  match P.rounds.length, m, ch.1, decoded P m T with
  | 31, .payload _, .queries r, some S =>
      S.card ≤ 9557 ∧ (Q22.chalSet r).card = 22 ∧ Q22.chalSet r ⊆ S
  | _, _, _, _ => False

def queryCap : ℚ := (Nat.choose 9557 22 : ℚ) / (Nat.choose 262144 22 : ℚ)

private theorem query_row_law (p : Params M Cv L) (hD : 5 ≤ p.D)
    (decoded : UnifiedSampler.Prefix M Cv L → Message M → Table (Addr L) State →
      Option (Finset (Fin 262144)))
    (T : Table (Addr L) State) (P : UnifiedSampler.Prefix M Cv L) (msg : M)
    (hround : P.rounds.length = 31) :
    independentMean (UnifiedSampler.samp p hD 31 P (.payload msg)).toProgram
      (fun w => indicator (queryBad decoded P (.payload msg) T w.2)) =
    mean (fun s : State => Q22.chainE
      (fun bs xs => indicator (queryBad decoded P (.payload msg) T
        (UnifiedSampler.liftQuery (Q22.scanOut 8 Q22.q0 bs xs s)))) 8) := by
  rw [UnifiedSampler.row_query]
  simp only [QuerySamplerBridge.sampler, Sampler.toProgram, independentMean]
  apply mean_congr
  intro s
  exact QueryBackgroundLaw.independent_chain_law p
    (fun bs xs => UnifiedSampler.liftQuery (Q22.scanOut 8 Q22.q0 bs xs s))
    (fun ch => indicator (queryBad decoded P (.payload msg) T ch)) 8 s [] []

theorem query_row_density_bound (p : Params M Cv L) (hD : 5 ≤ p.D)
    (decoded : UnifiedSampler.Prefix M Cv L → Message M → Table (Addr L) State →
      Option (Finset (Fin 262144)))
    (T : Table (Addr L) State) (P : UnifiedSampler.Prefix M Cv L) (msg : M)
    (hround : P.rounds.length = 31) :
    independentMean (UnifiedSampler.samp p hD 31 P (.payload msg)).toProgram
      (fun w => indicator (queryBad decoded P (.payload msg) T w.2)) ≤ queryCap := by
  rw [query_row_law p hD decoded T P msg hround]
  cases hd : decoded P (.payload msg) T with
  | none =>
      have hevent : ∀ s bs xs,
          queryBad decoded P (.payload msg) T
            (UnifiedSampler.liftQuery (Q22.scanOut 8 Q22.q0 bs xs s)) = False := by
        intro s bs xs
        simp [queryBad, hround, hd, UnifiedSampler.liftQuery]
      simp_rw [hevent, indicator_false, Q22.chainE_const, mean_const]
      unfold queryCap
      positivity
  | some S =>
      by_cases hS : S.card ≤ 9557
      · have hevent : ∀ s bs xs,
            queryBad decoded P (.payload msg) T
              (UnifiedSampler.liftQuery (Q22.scanOut 8 Q22.q0 bs xs s)) =
              ((Q22.chalSet (Q22.scanOut 8 Q22.q0 bs xs s).1).card = 22 ∧
                Q22.chalSet (Q22.scanOut 8 Q22.q0 bs xs s).1 ⊆ S) := by
          intro s bs xs
          simp [queryBad, hround, hd, hS, UnifiedSampler.liftQuery]
        unfold queryCap
        simp_rw [hevent]
        apply mean_mono
        intro s
        exact Q22.q22_bound s S hS
      · have hevent : ∀ s bs xs,
            queryBad decoded P (.payload msg) T
              (UnifiedSampler.liftQuery (Q22.scanOut 8 Q22.q0 bs xs s)) = False := by
          intro s bs xs
          simp [queryBad, hround, hd, hS, UnifiedSampler.liftQuery]
        simp_rw [hevent, indicator_false, Q22.chainE_const, mean_const]
        unfold queryCap
        positivity

theorem query_density_bound (p : Params M Cv L) (hD : 5 ≤ p.D)
    (decoded : UnifiedSampler.Prefix M Cv L → Message M → Table (Addr L) State →
      Option (Finset (Fin 262144))) :
    ∀ (T : Table (Addr L) State) (i : Nat) (P : UnifiedSampler.Prefix M Cv L)
      (m : Message M), i < 33 → P.rounds.length = i →
      independentMean (UnifiedSampler.samp p hD i P m).toProgram
        (fun w => indicator (queryBad decoded P m T w.2)) ≤ queryCap := by
  intro T i P m hi hround
  by_cases hi31 : i = 31
  · subst i
    rw [hround]
    cases m with
    | initial c1 =>
        have hz : ∀ w : View (Addr L) State (Challenge Cv),
            indicator (queryBad decoded P (.initial c1) T w.2) = 0 := by
          intro w
          rw [FS.indicator_iff (q := False), FS.indicator_false]
          intro hbad
          simp [queryBad] at hbad
        rw [independentMean_congr _ hz, independentMean_const]
        unfold queryCap
        positivity
    | payload msg =>
        exact query_row_density_bound p hD decoded T P msg hround
  · have hz : ∀ w : View (Addr L) State (Challenge Cv),
        indicator (queryBad decoded P m T w.2) = 0 := by
      intro w
      rw [FS.indicator_iff (q := False), FS.indicator_false]
      intro hbad
      cases m with
      | initial c1 => simp [queryBad] at hbad
      | payload msg =>
          simp [queryBad, hround, hi31] at hbad
    rw [independentMean_congr _ hz, independentMean_const]
    unfold queryCap
    positivity

#print axioms query_row_density_bound
#print axioms query_density_bound

end AspisR1.UnifiedQueryDensity
end
