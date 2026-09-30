import AspisV8R19.CirclePairPrefixProgram
import AspisV8R19.SamplerWrapperPolicies

/-! A small, typed selected-research prefix.

The circle pair is the existing `CirclePairPrefixProgram.program`, so its
secure-circle and distinct-retry `Except` errors are retained verbatim.  The
three later nonzero wrappers are explicit typed program parameters.  This is
only a deterministic program constructor; no source equivalence,
distribution, freshness, or security statement is asserted. -/
set_option autoImplicit false
namespace AspisV8R19.SelectedResearchPrefixProgram

open Aeneas Aeneas.Std Result
open DuplexFrames SourceDuplexStep SourceOraclePrograms
open MemoizedProgramLaw OracleProgramOps
open CirclePairPrefixProgram
open SamplerWrapperPolicies
noncomputable section

abbrev NonzeroResult := Except SamplerWrapperPolicies.Error (List Nat) × State

inductive Error where
  | circle (e : CircleError)
  | nonzero (e : SamplerWrapperPolicies.Error)

structure Config where
  vectorLabel : DuplexFrames.Byte
  vector0 : Bytes
  vector1 : Bytes
  nonzeroGamma : State → Program Bytes State NonzeroResult
  nonzeroKappa : State → Program Bytes State NonzeroResult
  nonzeroTau : State → Program Bytes State NonzeroResult

structure Output where
  first : Point
  second : Point
  gamma : List Nat
  kappa : List Nat
  tau : List Nat

abbrev Result := Except Error Output × State

def afterTau (first second : Point) (gamma kappa : List Nat)
    (t : NonzeroResult) : Program Bytes State Result :=
  match t.1 with
  | .error e => .done (.error (.nonzero e), t.2)
  | .ok tau =>
      .done (.ok (Output.mk first second gamma kappa tau), t.2)

def afterKappa (cfg : Config) (first second : Point) (gamma : List Nat)
    (k : NonzeroResult) : Program Bytes State Result :=
  match k.1 with
  | .error e => .done (.error (.nonzero e), k.2)
  | .ok kappa => bind (cfg.nonzeroTau k.2) (afterTau first second gamma kappa)

def afterGamma (cfg : Config) (first second : Point)
    (g : NonzeroResult) : Program Bytes State Result :=
  match g.1 with
  | .error e => .done (.error (.nonzero e), g.2)
  | .ok gamma => bind (cfg.nonzeroKappa g.2) (afterKappa cfg first second gamma)

def afterCircle (cfg : Config) (r : PairResult) : Program Bytes State Result :=
  match r.1 with
  | .error e => .done (.error (.circle e), r.2)
  | .ok (first, second) =>
      bind (cfg.nonzeroGamma r.2) (afterGamma cfg first second)

def selectedResearchPrefixProgram (cfg : Config) (s : State) :
    Program Bytes State Result :=
  bind (CirclePairPrefixProgram.program cfg.vectorLabel cfg.vector0 cfg.vector1 s)
    (afterCircle cfg)

theorem selected_circle_is_direct (cfg : Config) (s : State) :
    selectedResearchPrefixProgram cfg s =
      bind (CirclePairPrefixProgram.program cfg.vectorLabel cfg.vector0 cfg.vector1 s)
        (afterCircle cfg) := by
  rfl

#print axioms selected_circle_is_direct
end
end AspisV8R19.SelectedResearchPrefixProgram
