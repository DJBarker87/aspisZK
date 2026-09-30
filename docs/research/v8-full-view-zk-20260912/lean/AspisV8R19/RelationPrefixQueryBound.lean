import AspisV8R19.RelationPrefixProgram
import AspisV8R19.IndependentMeanFixedTapeQM31
import AspisV8R19.IndependentMeanFixedTapeCircle
import AspisV8R19.Q22SamplerProgram

/-! Raw fixed-tape query bounds for the typed relation prefix.

The component bounds are explicit premises.  This is only structural oracle
plumbing: it preserves all component outcomes and makes no source-equivalence,
freshness, distribution, or security claim. -/
set_option autoImplicit false
namespace AspisV8R19.RelationPrefixQueryBound

open DuplexFrames SourceDuplexStep SourceOraclePrograms
open MemoizedProgramLaw OracleProgramOps
open AspisV8R19.RelationPrefixProgram
open AspisV8R19.IndependentMeanFixedTape
open AspisV8R19.IndependentMeanFixedTapeQM31
open AspisV8R19.IndependentMeanFixedTapeCircle
open AspisV8R19.QM31SamplerProgram
open AspisV8R19.Q22SamplerProgram
open AspisV8R19.Q22WordScan AspisV8R19.SamplerWords

def absorbWithin {O : Type} (s : State) (label : DuplexFrames.Byte) (data : Bytes)
    (next : State → Program Bytes State O) (n : Nat)
    (hn : ∀ s, Within (next s) n) :
    Within (absorbThen s label data next) (1 + n) := by
  change Within (OracleProgramOps.bind (absorbProgram s label data) next) (1 + n)
  exact withinBind 1 n (absorbProgram s label data) next
    (Within.ask _ _ 0 (fun _ => Within.done _ 0)) hn

def challengeWithin {O : Type} (s : State)
    (next : State → Option (List Nat) → Program Bytes State O) (n : Nat)
    (hn : ∀ s a, Within (next s a) n) :
    Within (challengeThen s next) (66 + n) := by
  change Within (OracleProgramOps.bind (QM31SamplerProgram.challengeProgram s)
    (fun r => next r.2 r.1)) (66 + n)
  exact withinBind 66 n (QM31SamplerProgram.challengeProgram s)
    (fun r => next r.2 r.1) (challengeProgram_within s) (fun r => hn r.2 r.1)

def componentWithin {O : Type} (p : State → Program Bytes State ChallengeResult)
    (s : State) (next : State → Option (List Nat) → Program Bytes State O)
    (m n : Nat) (hp : ∀ s, Within (p s) m)
    (hn : ∀ s a, Within (next s a) n) :
    Within (componentThen p s next) (m + n) := by
  change Within (OracleProgramOps.bind (p s) (fun r => next r.2 r.1)) (m + n)
  exact withinBind m n (p s) (fun r => next r.2 r.1) (hp s)
    (fun r => hn r.2 r.1)

def q22LoopWithin (n : Nat) (s : State) (q : ScanState) :
    Within (loopProgram n s q) (2 * n) := by
  induction n generalizing s q with
  | zero => exact Within.done _ 0
  | succ n ih =>
      by_cases hd : q.draws < 64
      · simp only [loopProgram, hd]
        have h := withinBind 2 (2 * n) (squeezeProgram s)
          (fun p => if (scan q (words 18 p.1)).2
            then .done (finish (scan q (words 18 p.1)).1, p.2)
            else loopProgram n p.2 (scan q (words 18 p.1)).1)
          (Within.ask _ _ 1 (fun _ => Within.ask _ _ 0
            (fun _ => Within.done _ 0)))
          (fun p => by
            split
            · exact Within.done _ (2 * n)
            · exact ih p.2 (scan q (words 18 p.1)).1)
        change Within (OracleProgramOps.bind (squeezeProgram s) _) (2 * (n + 1))
        rw [show 2 * (n + 1) = 2 + 2 * n by omega]
        exact h
      · simp only [loopProgram, hd]
        exact Within.done _ (2 * (n + 1))

def q22ChallengeWithin (s : State) :
    Within (Q22SamplerProgram.challengeProgram s) 16 := by
  change Within (loopProgram 8 s ⟨[], 0⟩) (2 * 8)
  exact q22LoopWithin 8 s ⟨[], 0⟩

def relationPrefix_within
    (cfg : PrefixInput) (s : State)
    (hfirst : ∀ s, Within (cfg.firstCircle s) 198)
    (hsecond : ∀ first s, Within (cfg.secondDistinctCircle first s) 594)
    (hgamma : ∀ s, Within (cfg.nonzeroGamma s) 198)
    (hkappa : ∀ s, Within (cfg.nonzeroKappa s) 198)
    (htau : ∀ s, Within (cfg.nonzeroTau s) 198) :
    Within (relationPrefixProgram cfg s) 1600 := by
  unfold relationPrefixProgram
  apply absorbWithin _ _ _ _ 1599
  intro s1
  apply absorbWithin _ _ _ _ 1598
  intro s2
  apply absorbWithin _ _ _ _ 1597
  intro s3
  apply challengeWithin _ _ 1531
  intro s4 lambda
  apply challengeWithin _ _ 1465
  intro s5 chi
  apply absorbWithin _ _ _ _ 1464
  intro s6
  apply absorbWithin _ _ _ _ 1463
  intro s7
  apply componentWithin cfg.firstCircle _ _ 198 1265 hfirst
  intro s8 firstCircle
  apply absorbWithin _ _ _ _ 1264
  intro s9
  apply componentWithin (cfg.secondDistinctCircle firstCircle) _ _ 594 670
    (hsecond firstCircle)
  intro s10 secondCircle
  apply absorbWithin _ _ _ _ 669
  intro s11
  apply absorbWithin _ _ _ _ 668
  intro s12
  apply componentWithin cfg.nonzeroGamma _ _ 198 470 hgamma
  intro s13 gamma
  apply absorbWithin _ _ _ _ 469
  intro s14
  apply componentWithin cfg.nonzeroKappa _ _ 198 271 hkappa
  intro s15 kappa
  apply absorbWithin _ _ _ _ 270
  intro s16
  apply absorbWithin _ _ _ _ 269
  intro s17
  apply absorbWithin _ _ _ _ 268
  intro s18
  apply componentWithin cfg.nonzeroTau _ _ 198 70 htau
  intro s19 tau
  apply absorbWithin _ _ _ _ 69
  intro s20
  apply absorbWithin _ _ _ _ 68
  intro s21
  apply challengeWithin _ _ 2
  intro s22 alpha0
  apply absorbWithin _ _ _ _ 1
  intro s23
  apply absorbWithin _ _ _ _ 0
  intro s24
  exact Within.done _ 0

def throughRhoProgram (cfg : PrefixInput)
    (queryProfileLabel : DuplexFrames.Byte) (queryProfile : Bytes)
    (nonzeroRho : State → Program Bytes State ChallengeResult) (s : State) :
    Program Bytes State ChallengeResult :=
  OracleProgramOps.bind (relationPrefixProgram cfg s) (fun prefixOut =>
    OracleProgramOps.bind (Q22SamplerProgram.challengeProgram prefixOut.state) (fun q =>
      OracleProgramOps.bind
        (absorbProgram q.2 queryProfileLabel queryProfile) (fun s1 =>
          nonzeroRho s1)))

def throughRho_within
    (cfg : PrefixInput)
    (queryProfileLabel : DuplexFrames.Byte) (queryProfile : Bytes)
    (nonzeroRho : State → Program Bytes State ChallengeResult) (s : State)
    (hfirst : ∀ s, Within (cfg.firstCircle s) 198)
    (hsecond : ∀ first s, Within (cfg.secondDistinctCircle first s) 594)
    (hgamma : ∀ s, Within (cfg.nonzeroGamma s) 198)
    (hkappa : ∀ s, Within (cfg.nonzeroKappa s) 198)
    (htau : ∀ s, Within (cfg.nonzeroTau s) 198)
    (hrho : ∀ s, Within (nonzeroRho s) 198) :
    Within
      (throughRhoProgram cfg queryProfileLabel queryProfile nonzeroRho s) 1815 := by
  unfold throughRhoProgram
  apply withinBind 1600 215
    (relationPrefixProgram cfg s) _
    (relationPrefix_within cfg s hfirst hsecond hgamma hkappa htau)
  intro prefixOut
  apply withinBind 16 199
    (Q22SamplerProgram.challengeProgram prefixOut.state) _
    (q22ChallengeWithin prefixOut.state)
  intro q
  exact absorbWithin q.2 queryProfileLabel queryProfile nonzeroRho 198 hrho

#print axioms q22ChallengeWithin
#print axioms relationPrefix_within
#print axioms throughRho_within

end AspisV8R19.RelationPrefixQueryBound
