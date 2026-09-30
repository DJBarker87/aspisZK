import AspisV8R19.QM31SamplerProgram
import AspisV8R19.SourceOraclePrograms

/-! Typed source-order skeleton for the selected research callback prefix.

The exact plain QM31 calls are represented by `QM31SamplerProgram.challengeProgram`.
The callback's nonzero, secure-circle, and distinct-second wrappers are explicit
program parameters: this file supplies no wrapper implementation or law.  The
composition stops immediately before the q22 query sampler. -/
set_option autoImplicit false
namespace AspisV8R19.RelationPrefixProgram
open DuplexFrames SourceDuplexStep SourceOraclePrograms
open MemoizedProgramLaw OracleProgramOps
noncomputable section

abbrev ChallengeResult := Option (List Nat) × State

structure PrefixInput where
  -- relation_callback.rs:97-100
  profilePrefix : Byte
  profilePrefixData : Bytes
  statementLabel : Byte
  statement : Bytes
  rootLabel : Byte
  root : Bytes
  secondRootLabel : Byte
  secondRoot : Bytes
  pointClaimsLabel : Byte
  pointClaims : Bytes
  -- relation_callback.rs:105, 107
  oodVectorLabel : Byte
  oodVector0 : Bytes
  oodVector1 : Bytes
  -- relation_callback.rs:108-109
  paymentNonceLabel : Byte
  paymentNonce : Bytes
  inactiveClaimLabel : Byte
  inactiveClaim : Bytes
  -- relation_callback.rs:118-119
  ordinaryLabel : Byte
  ordinary : Bytes
  claimLabel : Byte
  claim : Bytes
  imageProfileLabel : Byte
  imageProfile : Bytes
  -- relation_callback.rs:283-285
  relationRoundLabel : Byte
  relationRound0 : Bytes
  foldNonceLabel : Byte
  foldNonce : Bytes
  -- relation_callback.rs:123
  final256Label : Byte
  final256 : Bytes
  grindNonceLabel : Byte
  grindNonce : Bytes
  -- Explicit components for wrappers not yet represented by exact constructors.
  firstCircle : State → Program Bytes State ChallengeResult
  secondDistinctCircle : Option (List Nat) → State → Program Bytes State ChallengeResult
  nonzeroGamma : State → Program Bytes State ChallengeResult
  nonzeroKappa : State → Program Bytes State ChallengeResult
  nonzeroTau : State → Program Bytes State ChallengeResult

structure PrefixOut where
  lambda : Option (List Nat)
  chi : Option (List Nat)
  firstCircle : Option (List Nat)
  secondCircle : Option (List Nat)
  gamma : Option (List Nat)
  kappa : Option (List Nat)
  tau : Option (List Nat)
  alpha0 : Option (List Nat)
  state : State

def absorbThen {O : Type} (s : State) (label : Byte) (data : Bytes)
    (next : State → Program Bytes State O) : Program Bytes State O :=
  bind (absorbProgram s label data) next

def challengeThen {O : Type} (s : State)
    (next : State → Option (List Nat) → Program Bytes State O) :
    Program Bytes State O :=
  bind (QM31SamplerProgram.challengeProgram s)
    (fun r => next r.2 r.1)

def componentThen {O : Type} (p : State → Program Bytes State ChallengeResult)
    (s : State) (next : State → Option (List Nat) → Program Bytes State O) :
    Program Bytes State O :=
  bind (p s) (fun r => next r.2 r.1)

def relationPrefixProgram (cfg : PrefixInput) (s : State) :
    Program Bytes State PrefixOut :=
  -- relation_callback.rs:97-100: profile, statement, root, lambda, chi,
  -- second root, and point claims.
  absorbThen s cfg.profilePrefix cfg.profilePrefixData (fun s1 =>
    absorbThen s1 cfg.statementLabel cfg.statement (fun s2 =>
      absorbThen s2 cfg.rootLabel cfg.root (fun s3 =>
        challengeThen s3 (fun s4 lambda =>
          challengeThen s4 (fun s5 chi =>
            absorbThen s5 cfg.secondRootLabel cfg.secondRoot (fun s6 =>
              absorbThen s6 cfg.pointClaimsLabel cfg.pointClaims (fun s7 =>
                -- relation_callback.rs:104-107: first OOD, vector-0 absorb,
                -- bounded distinct-second OOD wrapper, vector-1 absorb.
                componentThen cfg.firstCircle s7 (fun s8 firstCircle =>
                  absorbThen s8 cfg.oodVectorLabel cfg.oodVector0 (fun s9 =>
                    componentThen (cfg.secondDistinctCircle firstCircle) s9
                      (fun s10 secondCircle =>
                        absorbThen s10 cfg.oodVectorLabel cfg.oodVector1 (fun s11 =>
                          -- relation_callback.rs:108-109: nonce/gamma,
                          -- inactive claim/kappa.
                          absorbThen s11 cfg.paymentNonceLabel cfg.paymentNonce (fun s12 =>
                            componentThen cfg.nonzeroGamma s12 (fun s13 gamma =>
                              absorbThen s13 cfg.inactiveClaimLabel cfg.inactiveClaim (fun s14 =>
                                componentThen cfg.nonzeroKappa s14 (fun s15 kappa =>
                                  -- relation_callback.rs:118-120: ordinary,
                                  -- claim, image profile, and tau.
                                  absorbThen s15 cfg.ordinaryLabel cfg.ordinary (fun s16 =>
                                    absorbThen s16 cfg.claimLabel cfg.claim (fun s17 =>
                                      absorbThen s17 cfg.imageProfileLabel cfg.imageProfile (fun s18 =>
                                        componentThen cfg.nonzeroTau s18 (fun s19 tau =>
                                          -- relation_callback.rs:283-285:
                                          -- round 0, fold nonce, alpha[0].
                                          absorbThen s19 cfg.relationRoundLabel cfg.relationRound0 (fun s20 =>
                                            absorbThen s20 cfg.foldNonceLabel cfg.foldNonce (fun s21 =>
                                              challengeThen s21 (fun s22 alpha0 =>
                                                -- relation_callback.rs:123: FINAL256,
                                                -- then GRIND_NONCE.  Stop here.
                                                absorbThen s22 cfg.final256Label cfg.final256 (fun s23 =>
                                                  absorbThen s23 cfg.grindNonceLabel cfg.grindNonce (fun s24 =>
                                                    .done {
                                                      lambda := lambda
                                                      chi := chi
                                                      firstCircle := firstCircle
                                                      secondCircle := secondCircle
                                                      gamma := gamma
                                                      kappa := kappa
                                                      tau := tau
                                                      alpha0 := alpha0
                                                      state := s24 }))))))))))))))))))))))))

#print axioms relationPrefixProgram
end
end AspisV8R19.RelationPrefixProgram
