import R1UnifiedDecoderBound
import R1UnifiedProtocol
import AspisV8R19.R572SequentialWordMass

/-! The single unified decoder satisfies the existing v3 chain-density
interface whenever the unified protocol satisfies the existing D2 condition.
No concrete classifier, epsilon function, or numerical bound is assumed proved. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedChainDensity

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.R572SequentialWordMass
open TranscriptView

variable {M Cv W : Type} {L : Nat}

theorem chainDensity (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (rb : RoundByRound' (UnifiedSampler.Public L) (Message M) (Challenge Cv)
      (Addr L) State)
    (hD2 : FS2.D2 (UnifiedProtocol.protocol p hD extract) rb)
    (pub : UnifiedSampler.Public L) :
    ChainDensity3 (UnifiedProtocol.protocol p hD extract) rb
      (UnifiedDecoder.decode p hD pub) := by
  classical
  let pr := UnifiedProtocol.protocol p hD extract
  intro a T own pend g hd
  apply UnifiedDecoderBound.decoded_bound p hD pub a T own pend g hd
    (fun out => indicator (d2Bad pr rb out.1 out.2.1 T out.2.2))
    (maxErr rb.ε pr.r)
  intro n P m hn hround
  change independentMean (pr.samp n P m).toProgram
    (fun w => indicator (d2Bad pr rb P m T w.2)) ≤ maxErr rb.ε pr.r
  have hlt : P.round < pr.r := by
    change P.rounds.length < 33
    omega
  by_cases hex : ∃ T', rb.doomed P T'
  · obtain ⟨T', hdoom⟩ := hex
    calc
      _ = independentMean (pr.samp n P m).toProgram
          (fun w => indicator (¬ rb.doomed (P.ext m w.2) T)) := by
        apply independentMean_congr
        intro w
        apply indicator_iff
        exact ⟨fun h => h.2.2, fun h => ⟨hlt, ⟨T', hdoom⟩, h⟩⟩
      _ ≤ rb.ε n := hD2 n P m T' T hround hn hdoom
      _ ≤ maxErr rb.ε pr.r := le_maxErr rb.ε pr.r n hn
  · have hzero : ∀ w : View (Addr L) State (Challenge Cv),
        indicator (d2Bad pr rb P m T w.2) = 0 := by
      intro w
      rw [indicator_iff (q := False), indicator_false]
      exact ⟨fun h => hex h.2.1, False.elim⟩
    rw [independentMean_congr _ hzero, independentMean_const]
    exact maxErr_nonneg _ _

#print axioms chainDensity

end AspisR1.UnifiedChainDensity
end
