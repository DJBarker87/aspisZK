import AspisV8R19.RelationPrefixProgram
import AspisV8R19.CirclePairPrefixProgram
import AspisV8R19.SamplerWrapperPolicies
import AspisV8R19.Q22SamplerProgram

/-! Error-preserving typed schedule for the selected research callback through
rho.  This is a program skeleton only: it makes no source-equivalence,
privacy, distribution, or security claim. -/
set_option autoImplicit false
namespace AspisV8R19.SelectedResearchScheduleProgram

open DuplexFrames SourceDuplexStep SourceOraclePrograms
open MemoizedProgramLaw OracleProgramOps
open AspisV8R19.RelationPrefixProgram
open AspisV8R19.CirclePairPrefixProgram
open AspisV8R19.SamplerWrapperPolicies
open AspisV8R19.Q22SamplerProgram

inductive Error where
  | sampler
  | circle (e : CircleError)
  | nonzero (e : SamplerWrapperPolicies.Error)
  | q22 (e : Nat)

structure ScheduleOut where
  lambda : List Nat
  chi : List Nat
  circles : Point × Point
  gamma : List Nat
  kappa : List Nat
  tau : List Nat
  alpha : List Nat
  queries : List Nat
  rho : List Nat
  state : State

abbrev Result := Except Error ScheduleOut × State

def optionStep {X : Type} (failure : Error)
    (p : Program Bytes State (Option X × State))
    (k : X → State → Program Bytes State Result) :
    Program Bytes State Result :=
  bind p (fun r => match r.1 with
    | none => .done (Except.error failure, r.2)
    | some x => k x r.2)

def nonzeroStep {X : Type} (p : Program Bytes State
    (Except SamplerWrapperPolicies.Error X × State))
    (k : X → State → Program Bytes State Result) :
    Program Bytes State Result :=
  bind p (fun r => match r.1 with
    | .error e => .done (Except.error (.nonzero e), r.2)
    | .ok x => k x r.2)

def circleStep (p : Program Bytes State
    (Except CircleError (Point × Point) × State))
    (k : (Point × Point) → State → Program Bytes State Result) :
    Program Bytes State Result :=
  bind p (fun r => match r.1 with
    | .error e => .done (Except.error (.circle e), r.2)
    | .ok x => k x r.2)

def q22Step (p : Program Bytes State (Q22SamplerProgram.Result))
    (k : List Nat → State → Program Bytes State Result) :
    Program Bytes State Result :=
  bind p (fun r => match r.1 with
    | .error e => .done (Except.error (.q22 e), r.2)
    | .ok q => k q r.2)

def absorbStep (s : State) (label : DuplexFrames.Byte) (data : Bytes)
    (k : State → Program Bytes State Result) : Program Bytes State Result :=
  bind (absorbProgram s label data) k

def challengeStep (s : State)
    (k : List Nat → State → Program Bytes State Result) :
    Program Bytes State Result :=
  optionStep .sampler (QM31SamplerProgram.challengeProgram s) k

def afterQuery (cfg : PrefixInput) (queryProfileLabel : DuplexFrames.Byte)
    (queryProfileData : Bytes) (lambda chi : List Nat)
    (circles : Point × Point) (gamma kappa tau alpha queries : List Nat)
    (s : State) : Program Bytes State Result :=
  absorbStep s queryProfileLabel queryProfileData (fun s1 =>
    nonzeroStep (SamplerWrapperPolicies.nonzeroProgram s1) (fun rho s2 =>
      .done (Except.ok {
        lambda := lambda
        chi := chi
        circles := circles
        gamma := gamma
        kappa := kappa
        tau := tau
        alpha := alpha
        queries := queries
        rho := rho
        state := s2 }, s2)))

def afterAlpha (cfg : PrefixInput) (queryProfileLabel : DuplexFrames.Byte)
    (queryProfileData : Bytes) (lambda chi : List Nat)
    (circles : Point × Point) (gamma kappa tau alpha : List Nat)
    (s : State) : Program Bytes State Result :=
  absorbStep s cfg.final256Label cfg.final256 (fun s1 =>
    -- GRIND_NONCE is deliberately represented by its transcript absorb frame.
    absorbStep s1 cfg.grindNonceLabel cfg.grindNonce (fun s2 =>
      q22Step (Q22SamplerProgram.challengeProgram s2) (fun queries s3 =>
        afterQuery cfg queryProfileLabel queryProfileData lambda chi circles
          gamma kappa tau alpha queries s3)))

def afterTau (cfg : PrefixInput) (queryProfileLabel : DuplexFrames.Byte)
    (queryProfileData : Bytes) (lambda chi : List Nat)
    (circles : Point × Point) (gamma kappa tau : List Nat)
    (s : State) : Program Bytes State Result :=
  absorbStep s cfg.relationRoundLabel cfg.relationRound0 (fun s1 =>
    absorbStep s1 cfg.foldNonceLabel cfg.foldNonce (fun s2 =>
      challengeStep s2 (fun alpha s3 =>
        afterAlpha cfg queryProfileLabel queryProfileData lambda chi circles
          gamma kappa tau alpha s3)))

def afterKappa (cfg : PrefixInput) (queryProfileLabel : DuplexFrames.Byte)
    (queryProfileData : Bytes) (lambda chi : List Nat)
    (circles : Point × Point) (gamma kappa : List Nat)
    (s : State) : Program Bytes State Result :=
  absorbStep s cfg.ordinaryLabel cfg.ordinary (fun s1 =>
    absorbStep s1 cfg.claimLabel cfg.claim (fun s2 =>
      absorbStep s2 cfg.imageProfileLabel cfg.imageProfile (fun s3 =>
        nonzeroStep (SamplerWrapperPolicies.nonzeroProgram s3)
          (fun tau s4 => afterTau cfg queryProfileLabel queryProfileData
            lambda chi circles gamma kappa tau s4))))

def afterGamma (cfg : PrefixInput) (queryProfileLabel : DuplexFrames.Byte)
    (queryProfileData : Bytes) (lambda chi : List Nat)
    (circles : Point × Point) (gamma : List Nat) (s : State) :
    Program Bytes State Result :=
  absorbStep s cfg.inactiveClaimLabel cfg.inactiveClaim (fun s1 =>
    nonzeroStep (SamplerWrapperPolicies.nonzeroProgram s1)
      (fun kappa s2 => afterKappa cfg queryProfileLabel queryProfileData
        lambda chi circles gamma kappa s2))

def afterCircles (cfg : PrefixInput) (queryProfileLabel : DuplexFrames.Byte)
    (queryProfileData : Bytes) (lambda chi : List Nat)
    (circles : Point × Point) (s : State) : Program Bytes State Result :=
  absorbStep s cfg.paymentNonceLabel cfg.paymentNonce (fun s1 =>
    nonzeroStep (SamplerWrapperPolicies.nonzeroProgram s1)
      (fun gamma s2 => afterGamma cfg queryProfileLabel queryProfileData
        lambda chi circles gamma s2))

def program (cfg : PrefixInput) (queryProfileLabel : DuplexFrames.Byte)
    (queryProfileData : Bytes) (s : State) : Program Bytes State Result :=
  absorbStep s cfg.profilePrefix cfg.profilePrefixData (fun s1 =>
    absorbStep s1 cfg.statementLabel cfg.statement (fun s2 =>
      absorbStep s2 cfg.rootLabel cfg.root (fun s3 =>
        challengeStep s3 (fun lambda s4 =>
          challengeStep s4 (fun chi s5 =>
            absorbStep s5 cfg.secondRootLabel cfg.secondRoot (fun s6 =>
              absorbStep s6 cfg.pointClaimsLabel cfg.pointClaims (fun s7 =>
                circleStep (CirclePairPrefixProgram.program
                    cfg.oodVectorLabel cfg.oodVector0 cfg.oodVector1 s7)
                  (fun circles s8 => afterCircles cfg queryProfileLabel
                    queryProfileData lambda chi circles s8))))))))

#print axioms program

end AspisV8R19.SelectedResearchScheduleProgram
