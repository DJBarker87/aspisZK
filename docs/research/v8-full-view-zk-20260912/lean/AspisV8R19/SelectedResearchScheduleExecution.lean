import AspisV8R19.SelectedResearchScheduleProgram

/-! Explicit deterministic execution of the selected schedule.

The interpreter below is assembled from the already checked absorb, QM31,
circle-pair, nonzero and q22 runs. It does not define `run` as `eval`; the
`eval_run` theorem composes the component execution theorems. No Rust-source,
distribution, privacy or security claim is made here. -/
set_option autoImplicit false
namespace AspisV8R19.SelectedResearchScheduleExecution

open DuplexFrames SourceDuplexStep SourceOraclePrograms
open MemoizedProgramLaw OracleProgramOps
open AspisV8R19.RelationPrefixProgram
open AspisV8R19.SelectedResearchScheduleProgram

def bindView {I A X Y : Type} (r : View I A X)
    (k : X → View I A Y) : View I A Y :=
  let tail := k r.2
  (r.1 ++ tail.1, tail.2)

def optionRun {X : Type} (failure : SelectedResearchScheduleProgram.Error)
    (r : View Bytes State (Option X × State))
    (k : X → State → View Bytes State Result) : View Bytes State Result :=
  bindView r (fun out => match out.1 with
    | none => ([], (Except.error failure, out.2))
    | some x => k x out.2)

def nonzeroRun {X : Type}
    (r : View Bytes State (Except SamplerWrapperPolicies.Error X × State))
    (k : X → State → View Bytes State Result) : View Bytes State Result :=
  bindView r (fun out => match out.1 with
    | .error e => ([], (Except.error (.nonzero e), out.2))
    | .ok x => k x out.2)

def circleRun
    (r : View Bytes State
      (Except CirclePairPrefixProgram.CircleError
        (CirclePairPrefixProgram.Point × CirclePairPrefixProgram.Point) × State))
    (k : (CirclePairPrefixProgram.Point × CirclePairPrefixProgram.Point) →
      State → View Bytes State Result) : View Bytes State Result :=
  bindView r (fun out => match out.1 with
    | .error e => ([], (Except.error (.circle e), out.2))
    | .ok x => k x out.2)

def q22Run (r : View Bytes State Q22SamplerProgram.Result)
    (k : List Nat → State → View Bytes State Result) : View Bytes State Result :=
  bindView r (fun out => match out.1 with
    | .error e => ([], (Except.error (.q22 e), out.2))
    | .ok x => k x out.2)

def absorbRun (H : Bytes → State) (s : State) (label : DuplexFrames.Byte)
    (data : Bytes) (k : State → View Bytes State Result) :
    View Bytes State Result :=
  bindView (CirclePairPrefixProgram.absorbRun H label data s) k

def challengeRun (H : Bytes → State) (s : State)
    (k : List Nat → State → View Bytes State Result) :
    View Bytes State Result :=
  optionRun .sampler (QM31SamplerProgram.challengeRun H s) k

def afterQueryRun (cfg : PrefixInput) (ql : DuplexFrames.Byte) (qd : Bytes)
    (lambda chi : List Nat)
    (circles : CirclePairPrefixProgram.Point × CirclePairPrefixProgram.Point)
    (gamma kappa tau alpha queries : List Nat) (H : Bytes → State) (s : State) :
    View Bytes State Result :=
  absorbRun H s ql qd (fun s1 =>
    nonzeroRun (SamplerWrapperPolicies.nonzeroRun H s1) (fun rho s2 =>
      ([], (Except.ok {
        lambda := lambda
        chi := chi
        circles := circles
        gamma := gamma
        kappa := kappa
        tau := tau
        alpha := alpha
        queries := queries
        rho := rho
        state := s2 }, s2))))

def afterAlphaRun (cfg : PrefixInput) (ql : DuplexFrames.Byte) (qd : Bytes)
    (lambda chi : List Nat)
    (circles : CirclePairPrefixProgram.Point × CirclePairPrefixProgram.Point)
    (gamma kappa tau alpha : List Nat) (H : Bytes → State) (s : State) :
    View Bytes State Result :=
  absorbRun H s cfg.final256Label cfg.final256 (fun s1 =>
    absorbRun H s1 cfg.grindNonceLabel cfg.grindNonce (fun s2 =>
      q22Run (Q22SamplerProgram.challengeRun H s2) (fun queries s3 =>
        afterQueryRun cfg ql qd lambda chi circles gamma kappa tau alpha
          queries H s3)))

def afterTauRun (cfg : PrefixInput) (ql : DuplexFrames.Byte) (qd : Bytes)
    (lambda chi : List Nat)
    (circles : CirclePairPrefixProgram.Point × CirclePairPrefixProgram.Point)
    (gamma kappa tau : List Nat) (H : Bytes → State) (s : State) :
    View Bytes State Result :=
  absorbRun H s cfg.relationRoundLabel cfg.relationRound0 (fun s1 =>
    absorbRun H s1 cfg.foldNonceLabel cfg.foldNonce (fun s2 =>
      challengeRun H s2 (fun alpha s3 =>
        afterAlphaRun cfg ql qd lambda chi circles gamma kappa tau alpha H s3)))

def afterKappaRun (cfg : PrefixInput) (ql : DuplexFrames.Byte) (qd : Bytes)
    (lambda chi : List Nat)
    (circles : CirclePairPrefixProgram.Point × CirclePairPrefixProgram.Point)
    (gamma kappa : List Nat) (H : Bytes → State) (s : State) :
    View Bytes State Result :=
  absorbRun H s cfg.ordinaryLabel cfg.ordinary (fun s1 =>
    absorbRun H s1 cfg.claimLabel cfg.claim (fun s2 =>
      absorbRun H s2 cfg.imageProfileLabel cfg.imageProfile (fun s3 =>
        nonzeroRun (SamplerWrapperPolicies.nonzeroRun H s3) (fun tau s4 =>
          afterTauRun cfg ql qd lambda chi circles gamma kappa tau H s4))))

def afterGammaRun (cfg : PrefixInput) (ql : DuplexFrames.Byte) (qd : Bytes)
    (lambda chi : List Nat)
    (circles : CirclePairPrefixProgram.Point × CirclePairPrefixProgram.Point)
    (gamma : List Nat) (H : Bytes → State) (s : State) :
    View Bytes State Result :=
  absorbRun H s cfg.inactiveClaimLabel cfg.inactiveClaim (fun s1 =>
    nonzeroRun (SamplerWrapperPolicies.nonzeroRun H s1) (fun kappa s2 =>
      afterKappaRun cfg ql qd lambda chi circles gamma kappa H s2))

def afterCirclesRun (cfg : PrefixInput) (ql : DuplexFrames.Byte) (qd : Bytes)
    (lambda chi : List Nat)
    (circles : CirclePairPrefixProgram.Point × CirclePairPrefixProgram.Point)
    (H : Bytes → State) (s : State) : View Bytes State Result :=
  absorbRun H s cfg.paymentNonceLabel cfg.paymentNonce (fun s1 =>
    nonzeroRun (SamplerWrapperPolicies.nonzeroRun H s1) (fun gamma s2 =>
      afterGammaRun cfg ql qd lambda chi circles gamma H s2))

def run (cfg : PrefixInput) (ql : DuplexFrames.Byte) (qd : Bytes)
    (H : Bytes → State) (s : State) : View Bytes State Result :=
  absorbRun H s cfg.profilePrefix cfg.profilePrefixData (fun s1 =>
    absorbRun H s1 cfg.statementLabel cfg.statement (fun s2 =>
      absorbRun H s2 cfg.rootLabel cfg.root (fun s3 =>
        challengeRun H s3 (fun lambda s4 =>
          challengeRun H s4 (fun chi s5 =>
            absorbRun H s5 cfg.secondRootLabel cfg.secondRoot (fun s6 =>
              absorbRun H s6 cfg.pointClaimsLabel cfg.pointClaims (fun s7 =>
                circleRun (CirclePairPrefixProgram.run H cfg.oodVectorLabel
                  cfg.oodVector0 cfg.oodVector1 s7) (fun circles s8 =>
                    afterCirclesRun cfg ql qd lambda chi circles H s8))))))))

theorem optionStep_exact {X : Type} (failure : SelectedResearchScheduleProgram.Error)
    (p : Program Bytes State (Option X × State))
    (k : X → State → Program Bytes State Result) (H : Bytes → State) :
    eval H (optionStep failure p k) =
      optionRun failure (eval H p) (fun x s => eval H (k x s)) := by
  simp only [optionStep, eval_bind, optionRun, bindView]
  cases h : (eval H p).2.1 <;> rfl

theorem nonzeroStep_exact {X : Type}
    (p : Program Bytes State (Except SamplerWrapperPolicies.Error X × State))
    (k : X → State → Program Bytes State Result) (H : Bytes → State) :
    eval H (nonzeroStep p k) =
      nonzeroRun (eval H p) (fun x s => eval H (k x s)) := by
  simp only [nonzeroStep, eval_bind, nonzeroRun, bindView]
  cases h : (eval H p).2.1 <;> rfl

theorem circleStep_exact
    (p : Program Bytes State
      (Except CirclePairPrefixProgram.CircleError
        (CirclePairPrefixProgram.Point × CirclePairPrefixProgram.Point) × State))
    (k : (CirclePairPrefixProgram.Point × CirclePairPrefixProgram.Point) →
      State → Program Bytes State Result) (H : Bytes → State) :
    eval H (circleStep p k) =
      circleRun (eval H p) (fun x s => eval H (k x s)) := by
  simp only [circleStep, eval_bind, circleRun, bindView]
  cases h : (eval H p).2.1 <;> rfl

theorem q22Step_exact (p : Program Bytes State Q22SamplerProgram.Result)
    (k : List Nat → State → Program Bytes State Result) (H : Bytes → State) :
    eval H (q22Step p k) =
      q22Run (eval H p) (fun x s => eval H (k x s)) := by
  simp only [q22Step, eval_bind, q22Run, bindView]
  cases h : (eval H p).2.1 <;> rfl

theorem absorbStep_exact (s : State) (label : DuplexFrames.Byte) (data : Bytes)
    (k : State → Program Bytes State Result) (H : Bytes → State) :
    eval H (absorbStep s label data k) =
      absorbRun H s label data (fun s => eval H (k s)) := by
  simp [absorbStep, absorbRun, bindView, eval_bind,
    CirclePairPrefixProgram.absorbRun, SourceOraclePrograms.absorb_eval]

theorem challengeStep_exact (s : State)
    (k : List Nat → State → Program Bytes State Result) (H : Bytes → State) :
    eval H (challengeStep s k) =
      challengeRun H s (fun x s => eval H (k x s)) := by
  unfold challengeStep challengeRun
  rw [optionStep_exact, QM31SamplerProgram.challenge_exact]

theorem afterQuery_exact (cfg : PrefixInput) (ql : DuplexFrames.Byte) (qd : Bytes)
    (lambda chi : List Nat)
    (circles : CirclePairPrefixProgram.Point × CirclePairPrefixProgram.Point)
    (gamma kappa tau alpha queries : List Nat) (H : Bytes → State) (s : State) :
    eval H (afterQuery cfg ql qd lambda chi circles gamma kappa tau alpha queries s) =
      afterQueryRun cfg ql qd lambda chi circles gamma kappa tau alpha queries H s := by
  unfold afterQuery afterQueryRun
  rw [absorbStep_exact]
  simp only [nonzeroStep_exact, SamplerWrapperPolicies.nonzero_exact, eval]

theorem afterAlpha_exact (cfg : PrefixInput) (ql : DuplexFrames.Byte) (qd : Bytes)
    (lambda chi : List Nat)
    (circles : CirclePairPrefixProgram.Point × CirclePairPrefixProgram.Point)
    (gamma kappa tau alpha : List Nat) (H : Bytes → State) (s : State) :
    eval H (afterAlpha cfg ql qd lambda chi circles gamma kappa tau alpha s) =
      afterAlphaRun cfg ql qd lambda chi circles gamma kappa tau alpha H s := by
  unfold afterAlpha afterAlphaRun
  rw [absorbStep_exact]
  simp only [absorbStep_exact, q22Step_exact, Q22SamplerProgram.challenge_exact,
    afterQuery_exact]

theorem afterTau_exact (cfg : PrefixInput) (ql : DuplexFrames.Byte) (qd : Bytes)
    (lambda chi : List Nat)
    (circles : CirclePairPrefixProgram.Point × CirclePairPrefixProgram.Point)
    (gamma kappa tau : List Nat) (H : Bytes → State) (s : State) :
    eval H (afterTau cfg ql qd lambda chi circles gamma kappa tau s) =
      afterTauRun cfg ql qd lambda chi circles gamma kappa tau H s := by
  unfold afterTau afterTauRun
  rw [absorbStep_exact]
  simp only [absorbStep_exact, challengeStep_exact, afterAlpha_exact]

theorem afterKappa_exact (cfg : PrefixInput) (ql : DuplexFrames.Byte) (qd : Bytes)
    (lambda chi : List Nat)
    (circles : CirclePairPrefixProgram.Point × CirclePairPrefixProgram.Point)
    (gamma kappa : List Nat) (H : Bytes → State) (s : State) :
    eval H (afterKappa cfg ql qd lambda chi circles gamma kappa s) =
      afterKappaRun cfg ql qd lambda chi circles gamma kappa H s := by
  unfold afterKappa afterKappaRun
  rw [absorbStep_exact]
  simp only [absorbStep_exact, nonzeroStep_exact,
    SamplerWrapperPolicies.nonzero_exact, afterTau_exact]

theorem afterGamma_exact (cfg : PrefixInput) (ql : DuplexFrames.Byte) (qd : Bytes)
    (lambda chi : List Nat)
    (circles : CirclePairPrefixProgram.Point × CirclePairPrefixProgram.Point)
    (gamma : List Nat) (H : Bytes → State) (s : State) :
    eval H (afterGamma cfg ql qd lambda chi circles gamma s) =
      afterGammaRun cfg ql qd lambda chi circles gamma H s := by
  unfold afterGamma afterGammaRun
  rw [absorbStep_exact]
  simp only [nonzeroStep_exact, SamplerWrapperPolicies.nonzero_exact, afterKappa_exact]

theorem afterCircles_exact (cfg : PrefixInput) (ql : DuplexFrames.Byte) (qd : Bytes)
    (lambda chi : List Nat)
    (circles : CirclePairPrefixProgram.Point × CirclePairPrefixProgram.Point)
    (H : Bytes → State) (s : State) :
    eval H (afterCircles cfg ql qd lambda chi circles s) =
      afterCirclesRun cfg ql qd lambda chi circles H s := by
  unfold afterCircles afterCirclesRun
  rw [absorbStep_exact]
  simp only [nonzeroStep_exact, SamplerWrapperPolicies.nonzero_exact, afterGamma_exact]

theorem eval_run (cfg : PrefixInput) (ql : DuplexFrames.Byte) (qd : Bytes)
    (H : Bytes → State) (s : State) :
    eval H (SelectedResearchScheduleProgram.program cfg ql qd s) =
      run cfg ql qd H s := by
  unfold SelectedResearchScheduleProgram.program run
  rw [absorbStep_exact]
  simp only [absorbStep_exact, challengeStep_exact, circleStep_exact,
    CirclePairPrefixProgram.eval_run, afterCircles_exact]

#print axioms optionStep_exact
#print axioms nonzeroStep_exact
#print axioms circleStep_exact
#print axioms q22Step_exact
#print axioms absorbStep_exact
#print axioms challengeStep_exact
#print axioms afterQuery_exact
#print axioms afterAlpha_exact
#print axioms afterTau_exact
#print axioms afterKappa_exact
#print axioms afterGamma_exact
#print axioms afterCircles_exact
#print axioms eval_run

end AspisV8R19.SelectedResearchScheduleExecution
