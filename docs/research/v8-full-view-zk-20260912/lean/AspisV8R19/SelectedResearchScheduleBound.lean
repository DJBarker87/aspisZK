import AspisV8R19.SelectedResearchScheduleProgram
import AspisV8R19.IndependentMeanFixedTapeCircle
import AspisV8R19.RelationPrefixQueryBound

/-! Structural fixed-tape bound for the selected research schedule.  This is
only raw oracle-read plumbing; all success/error branches remain visible and
no source, distribution, privacy, or security claim is made. -/
set_option autoImplicit false
namespace AspisV8R19.SelectedResearchScheduleBound

open DuplexFrames SourceDuplexStep SourceOraclePrograms
open MemoizedProgramLaw OracleProgramOps
open AspisV8R19.RelationPrefixProgram
open AspisV8R19.IndependentMeanFixedTape
open AspisV8R19.IndependentMeanFixedTapeQM31
open AspisV8R19.IndependentMeanFixedTapeCircle
open AspisV8R19.RelationPrefixQueryBound
open AspisV8R19.SelectedResearchScheduleProgram
open AspisV8R19.CirclePairPrefixProgram
open AspisV8R19.QM31SamplerProgram
open AspisV8R19.SamplerWrapperPolicies

def optionWithin {X : Type} (failure : SelectedResearchScheduleProgram.Error)
    (p : Program Bytes State (Option X × State))
    (k : X → State → Program Bytes State Result)
    (m n : Nat) (hp : Within p m)
    (hk : ∀ x s, Within (k x s) n) :
    Within (optionStep failure p k) (m + n) := by
  change Within (OracleProgramOps.bind p (fun r => match r.1 with
    | none => .done (Except.error failure, r.2)
    | some x => k x r.2)) (m + n)
  exact withinBind m n p (fun r => match r.1 with
    | none => .done (Except.error failure, r.2)
    | some x => k x r.2) hp (fun r => by
      cases r.1 with
      | none => exact Within.done _ n
      | some x => exact hk x r.2)

def nonzeroWithin {X : Type}
    (p : Program Bytes State (Except SamplerWrapperPolicies.Error X × State))
    (k : X → State → Program Bytes State Result)
    (m n : Nat) (hp : Within p m)
    (hk : ∀ x s, Within (k x s) n) :
    Within (nonzeroStep p k) (m + n) := by
  change Within (OracleProgramOps.bind p (fun r => match r.1 with
    | .error e => .done (Except.error (.nonzero e), r.2)
    | .ok x => k x r.2)) (m + n)
  exact withinBind m n p (fun r => match r.1 with
    | .error e => .done (Except.error (.nonzero e), r.2)
    | .ok x => k x r.2) hp (fun r => by
      cases r.1 with
      | error e => exact Within.done _ n
      | ok x => exact hk x r.2)

def circleWithin
    (p : Program Bytes State
      (Except CirclePairPrefixProgram.CircleError
        (CirclePairPrefixProgram.Point × CirclePairPrefixProgram.Point) × State))
    (k : (CirclePairPrefixProgram.Point × CirclePairPrefixProgram.Point) →
      State → Program Bytes State Result)
    (m n : Nat) (hp : Within p m)
    (hk : ∀ x s, Within (k x s) n) :
    Within (circleStep p k) (m + n) := by
  change Within (OracleProgramOps.bind p (fun r => match r.1 with
    | .error e => .done (Except.error (.circle e), r.2)
    | .ok x => k x r.2)) (m + n)
  exact withinBind m n p (fun r => match r.1 with
    | .error e => .done (Except.error (.circle e), r.2)
    | .ok x => k x r.2) hp (fun r => by
      cases r.1 with
      | error e => exact Within.done _ n
      | ok x => exact hk x r.2)

def q22Within (p : Program Bytes State Q22SamplerProgram.Result)
    (k : List Nat → State → Program Bytes State Result)
    (m n : Nat) (hp : Within p m)
    (hk : ∀ x s, Within (k x s) n) :
    Within (q22Step p k) (m + n) := by
  change Within (OracleProgramOps.bind p (fun r => match r.1 with
    | .error e => .done (Except.error (.q22 e), r.2)
    | .ok x => k x r.2)) (m + n)
  exact withinBind m n p (fun r => match r.1 with
    | .error e => .done (Except.error (.q22 e), r.2)
    | .ok x => k x r.2) hp (fun r => by
      cases r.1 with
      | error e => exact Within.done _ n
      | ok x => exact hk x r.2)

def absorbWithin (s : State) (label : DuplexFrames.Byte) (data : Bytes)
    (k : State → Program Bytes State Result) (n : Nat)
    (hk : ∀ s, Within (k s) n) :
    Within (absorbStep s label data k) (1 + n) := by
  change Within (OracleProgramOps.bind (absorbProgram s label data) k) (1 + n)
  exact withinBind 1 n (absorbProgram s label data) k
    (Within.ask _ _ 0 (fun _ => Within.done _ 0)) hk

def nonzeroCert (hc : ∀ s, Within (QM31SamplerProgram.challengeProgram s) 66)
    (s : State) : Within (SamplerWrapperPolicies.nonzeroProgram s) 198 := by
  change Within (BoundedSamplerWrapper.program
    SamplerWrapperPolicies.nonzeroAccept SamplerWrapperPolicies.Error.challengeExhausted
    SamplerWrapperPolicies.Error.challengeExhausted 3 s) 198
  exact boundedProgram_within _ _ _ hc 3 s

def afterQueryWithin (cfg : PrefixInput) (ql : DuplexFrames.Byte) (qd : Bytes)
    (lambda chi : List Nat)
    (circles : CirclePairPrefixProgram.Point × CirclePairPrefixProgram.Point)
    (gamma kappa tau alpha queries : List Nat) (s : State)
    (hc : ∀ s, Within (QM31SamplerProgram.challengeProgram s) 66) :
    Within (afterQuery cfg ql qd lambda chi circles gamma kappa tau alpha queries s) 199 := by
  unfold afterQuery
  apply absorbWithin _ _ _ _ 198
  intro s1
  apply nonzeroWithin _ _ 198 0 (nonzeroCert hc s1)
  intro rho s2
  exact Within.done _ 0

def afterAlphaWithin (cfg : PrefixInput) (ql : DuplexFrames.Byte) (qd : Bytes)
    (lambda chi : List Nat)
    (circles : CirclePairPrefixProgram.Point × CirclePairPrefixProgram.Point)
    (gamma kappa tau alpha : List Nat) (s : State)
    (hc : ∀ s, Within (QM31SamplerProgram.challengeProgram s) 66) :
    Within (afterAlpha cfg ql qd lambda chi circles gamma kappa tau alpha s) 217 := by
  unfold afterAlpha
  apply absorbWithin _ _ _ _ 216
  intro s1
  apply absorbWithin _ _ _ _ 215
  intro s2
  apply q22Within _ _ 16 199 (q22ChallengeWithin s2)
  intro queries s3
  exact afterQueryWithin cfg ql qd lambda chi circles gamma kappa tau alpha queries s3 hc

def afterTauWithin (cfg : PrefixInput) (ql : DuplexFrames.Byte) (qd : Bytes)
    (lambda chi : List Nat)
    (circles : CirclePairPrefixProgram.Point × CirclePairPrefixProgram.Point)
    (gamma kappa tau : List Nat) (s : State)
    (hc : ∀ s, Within (QM31SamplerProgram.challengeProgram s) 66) :
    Within (afterTau cfg ql qd lambda chi circles gamma kappa tau s) 285 := by
  unfold afterTau challengeStep
  apply absorbWithin _ _ _ _ 284
  intro s1
  apply absorbWithin _ _ _ _ 283
  intro s2
  apply optionWithin .sampler _ _ 66 217 (hc s2)
  intro alpha s3
  exact afterAlphaWithin cfg ql qd lambda chi circles gamma kappa tau alpha s3 hc

def afterKappaWithin (cfg : PrefixInput) (ql : DuplexFrames.Byte) (qd : Bytes)
    (lambda chi : List Nat)
    (circles : CirclePairPrefixProgram.Point × CirclePairPrefixProgram.Point)
    (gamma kappa : List Nat) (s : State)
    (hc : ∀ s, Within (QM31SamplerProgram.challengeProgram s) 66) :
    Within (afterKappa cfg ql qd lambda chi circles gamma kappa s) 486 := by
  unfold afterKappa
  apply absorbWithin _ _ _ _ 485
  intro s1
  apply absorbWithin _ _ _ _ 484
  intro s2
  apply absorbWithin _ _ _ _ 483
  intro s3
  apply nonzeroWithin _ _ 198 285 (nonzeroCert hc s3)
  intro tau s4
  exact afterTauWithin cfg ql qd lambda chi circles gamma kappa tau s4 hc

def afterGammaWithin (cfg : PrefixInput) (ql : DuplexFrames.Byte) (qd : Bytes)
    (lambda chi : List Nat)
    (circles : CirclePairPrefixProgram.Point × CirclePairPrefixProgram.Point)
    (gamma : List Nat) (s : State)
    (hc : ∀ s, Within (QM31SamplerProgram.challengeProgram s) 66) :
    Within (afterGamma cfg ql qd lambda chi circles gamma s) 685 := by
  unfold afterGamma
  apply absorbWithin _ _ _ _ 684
  intro s1
  apply nonzeroWithin _ _ 198 486 (nonzeroCert hc s1)
  intro kappa s2
  exact afterKappaWithin cfg ql qd lambda chi circles gamma kappa s2 hc

def afterCirclesWithin (cfg : PrefixInput) (ql : DuplexFrames.Byte) (qd : Bytes)
    (lambda chi : List Nat)
    (circles : CirclePairPrefixProgram.Point × CirclePairPrefixProgram.Point) (s : State)
    (hc : ∀ s, Within (QM31SamplerProgram.challengeProgram s) 66) :
    Within (afterCircles cfg ql qd lambda chi circles s) 884 := by
  unfold afterCircles
  apply absorbWithin _ _ _ _ 883
  intro s1
  apply nonzeroWithin _ _ 198 685 (nonzeroCert hc s1)
  intro gamma s2
  exact afterGammaWithin cfg ql qd lambda chi circles gamma s2 hc

def program_within (cfg : PrefixInput) (ql : DuplexFrames.Byte)
    (qd : Bytes) (s : State) :
    Within (SelectedResearchScheduleProgram.program cfg ql qd s) 1815 := by
  unfold SelectedResearchScheduleProgram.program challengeStep
  apply absorbWithin _ _ _ _ 1814
  intro s1
  apply absorbWithin _ _ _ _ 1813
  intro s2
  apply absorbWithin _ _ _ _ 1812
  intro s3
  apply optionWithin .sampler _ _ 66 1746 (challengeProgram_within s3)
  intro lambda s4
  apply optionWithin .sampler _ _ 66 1680 (challengeProgram_within s4)
  intro chi s5
  apply absorbWithin _ _ _ _ 1679
  intro s6
  apply absorbWithin _ _ _ _ 1678
  intro s7
  apply circleWithin _ _ 794 884
    (circlePair_within challengeProgram_within cfg.oodVectorLabel
      cfg.oodVector0 cfg.oodVector1 s7)
  intro circles s8
  exact afterCirclesWithin cfg ql qd lambda chi circles s8 challengeProgram_within

#print axioms afterQueryWithin
#print axioms afterAlphaWithin
#print axioms afterTauWithin
#print axioms afterKappaWithin
#print axioms afterGammaWithin
#print axioms afterCirclesWithin
#print axioms program_within

end AspisV8R19.SelectedResearchScheduleBound
