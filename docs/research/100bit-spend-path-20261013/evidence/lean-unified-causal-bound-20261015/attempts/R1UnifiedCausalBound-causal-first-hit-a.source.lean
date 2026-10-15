import R1UnifiedDecoderBound
import R0C.V3.Gen
import AspisV8R19.MemoizedProgramLaw

/-! A direct causal first-hit adapter for the unified background decoder.
This proves a conditional density-to-hit bound only; it supplies no concrete
bad-event density or acceptance-to-hit/extraction statement. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedCausalBound

open FS FS2 R0C.V3
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

variable {M Cv W : Type} {L : Nat}

theorem first_hit_bound (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L)
    (bad : UnifiedSampler.Prefix M Cv L → Message M →
      Table (Addr L) State → Challenge Cv → Prop)
    (B : ℚ) (hB : 0 ≤ B)
    (hfixed : ∀ (T : Table (Addr L) State) (i : Nat)
      (P : UnifiedSampler.Prefix M Cv L) (m : Message M),
      i < 33 → P.rounds.length = i →
      independentMean (UnifiedSampler.samp p hD i P m).toProgram
        (fun w => indicator (bad P m T w.2)) ≤ B)
    (q : Program (Addr L) State (Pf × Bool)) (t : Table (Addr L) State)
    (N : Nat) (hN : FirstReadsBound q t N) :
    lazyMean q t (fun v =>
      indicator (hitsChain3 (UnifiedDecoder.decode p hD pub) bad t v.1)) ≤ (N : ℚ) * B := by
  have hbad : ∀ (a : Addr L) (T : Table (Addr L) State) own pend g,
      UnifiedDecoder.decode p hD pub a T = some (own, pend, g) →
      blaw g (fun out => indicator (bad out.1 out.2.1 T out.2.2)) own pend ≤ B := by
    intro a T own pend g hdecode
    apply UnifiedDecoderBound.decoded_bound p hD pub a T own pend g hdecode
      (fun out => indicator (bad out.1 out.2.1 T out.2.2)) B
    intro i P m hi hround
    exact hfixed T i P m hi hround
  exact lemmaA3 (UnifiedDecoder.decode p hD pub) bad B q t N hB hbad hN

theorem empty_oracle_first_hit_bound (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L)
    (bad : UnifiedSampler.Prefix M Cv L → Message M →
      Table (Addr L) State → Challenge Cv → Prop)
    (B : ℚ) (hB : 0 ≤ B)
    (hfixed : ∀ (T : Table (Addr L) State) (i : Nat)
      (P : UnifiedSampler.Prefix M Cv L) (m : Message M),
      i < 33 → P.rounds.length = i →
      independentMean (UnifiedSampler.samp p hD i P m).toProgram
        (fun w => indicator (bad P m T w.2)) ≤ B)
    (q : Program (Addr L) State (Pf × Bool)) (N : Nat)
    (hQ : ∀ H : Addr L → State, FS2.distinctFirstReads (eval H q) ≤ N) :
    mean (fun H : Addr L → State =>
      indicator (hitsChain3 (UnifiedDecoder.decode p hD pub) bad emptyTable
        (eval H q).1)) ≤ (N : ℚ) * B := by
  have hfirst : FirstReadsBound q (emptyTable : Table (Addr L) State) N := by
    apply firstReadsBound_of_traces q emptyTable N
    intro H
    have h := hQ H
    have hc : complete (emptyTable : Table (Addr L) State) H = H := rfl
    rw [hc]
    simpa [FS2.distinctFirstReads] using h
  rw [empty_oracle_law q (fun v =>
    indicator (hitsChain3 (UnifiedDecoder.decode p hD pub) bad emptyTable v.1))]
  exact first_hit_bound p hD pub bad B hB hfixed q emptyTable N hfirst

#print axioms first_hit_bound
#print axioms empty_oracle_first_hit_bound

end AspisR1.UnifiedCausalBound
end
