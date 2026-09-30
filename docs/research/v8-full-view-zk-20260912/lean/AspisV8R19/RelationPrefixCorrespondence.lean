import AspisV8R19.RelationPrefixProgram
import AspisV8R19.CirclePairPrefixProgram
import AspisV8R19.Q22SamplerProgram

/-! Typed correspondence boundary for the selected research callback.

This file is deliberately a skeleton.  It records the exact shape of the
missing deterministic source-to-program bridge without asserting it.  The
Rust chronology is:

* `relation_callback.rs:97-100`: PROFILE, STATEMENT, ROOT, lambda, chi,
  SECOND_PHASE_ROOT, and V6_POINT_CLAIMS;
* `:104-107`: first secure circle, vector-0 absorb, up to three distinct
  second-circle attempts, then vector-1 absorb; sampler and exhaustion errors
  remain visible;
* `:108-114`: payment nonce/gamma, inactive-claim/kappa, and chord data;
* `:118-120`: ordinary, claim, image profile, and nonzero tau;
* `:283-285`: compact round 0, fold nonce, and alpha[0];
* `:286` / `:123-125`: FINAL256, GRIND_NONCE, q22 without replacement, and rho.

The existing `RelationPrefixProgram` exposes nonzero/circle wrappers as
parameterized components and returns `Option` observations, whereas the Rust
callback has typed sampler/domain/terminal failures.  This mismatch is kept
explicit below; no callback equivalence or security premise is claimed. -/
set_option autoImplicit false
namespace AspisV8R19.RelationPrefixCorrespondence

open MemoizedProgramLaw
open AspisV8R19.RelationPrefixProgram
open DuplexFrames SourceDuplexStep

variable {E : Type}

structure SourcePrefixResult (E : Type) (X : Type) where
  trace : List (Bytes × State)
  outcome : Except E X
  state : State

def modelPrefixResult (cfg : PrefixInput) (s : State) (H : Bytes → State) :
    SourcePrefixResult E PrefixOut :=
  let v := eval H (relationPrefixProgram cfg s)
  { trace := v.1
    outcome := Except.ok v.2
    state := v.2.state }

structure BridgePremise (E : Type) where
  sourceRun : PrefixInput → State → (Bytes → State) →
    SourcePrefixResult E PrefixOut
  -- This is the unproved source-to-model obligation.  In particular, it
  -- must preserve every failure, retry exhaustion, absorb, and state.
  exact : ∀ cfg s H, sourceRun cfg s H = modelPrefixResult cfg s H

def sourcePrefixView (b : BridgePremise E)
    (cfg : PrefixInput) (s : State) (H : Bytes → State) :
    SourcePrefixResult E PrefixOut :=
  let r := b.sourceRun cfg s H
  { trace := r.trace
    outcome := r.outcome
    state := r.state }

theorem source_prefix_correspondence
    (b : BridgePremise E) (cfg : PrefixInput)
    (s : State) (H : Bytes → State) :
    sourcePrefixView b cfg s H = modelPrefixResult cfg s H := by
  exact b.exact cfg s H

#print axioms source_prefix_correspondence

end AspisV8R19.RelationPrefixCorrespondence
