import FSOODSampler
import FSChallengeCanonical
import AspisFormal.K1.V7Tag73SecureCircleMap
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.FSV7OODSampler
open FSOracleExecution FSBoundedTranscript FSOODSampler
open AspisV5ComponentCQM31TowerExact
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73SecureCircleMap
noncomputable section

/-- Canonical limbs in the actual Rust c0.a,c0.b,c1.a,c1.b order. Invalid
length/range is rejected rather than silently reduced modulo p. -/
def assemble : List Nat → Option QM31Exact
  | [a,b,c,d] =>
      if h : a < P ∧ b < P ∧ c < P ∧ d < P then
        some (limbsToQM31Exact ![⟨a,h.1⟩,⟨b,h.2.1⟩,⟨c,h.2.2.1⟩,⟨d,h.2.2.2⟩])
      else none
  | _ => none

def decodePoint (limbs : List Nat) : Option SecureCirclePointBytes :=
  (assemble limbs).bind exactSecureCirclePointFromDecoded

theorem assemble_total_on_canonical (xs : List Nat) (len : xs.length = 4)
    (bounded : ∀ x ∈ xs, x < P) : ∃ parameter, assemble xs = some parameter := by
  match xs with
  | [] => cases len
  | [_] => cases len
  | [_,_] => cases len
  | [_,_,_] => cases len
  | [a,b,c,d] =>
      have h : a < P ∧ b < P ∧ c < P ∧ d < P :=
        ⟨bounded a (by simp), bounded b (by simp),
          bounded c (by simp), bounded d (by simp)⟩
      simp only [assemble, dif_pos h]
      exact ⟨_, rfl⟩
  | _::_::_::_::_::_ => simp only [List.length_cons] at len; omega

/-- The range/shape guard is not an extra rejection of a successful source
draw: its canonical four-limb invariant is proved from the literal sampler. -/
theorem challenge_assembles (tape : Tape) (s : Transcript) (xs : List Nat)
    (success : (challenge tape s).1 = some xs) :
    ∃ parameter, assemble xs = some parameter := by
  have canonical := FSChallengeCanonical.challenge_canonical tape s xs success
  exact assemble_total_on_canonical xs canonical.1 canonical.2

/-- Reuses the proved V7 literal tower rational map. The inverse check is
performed before exclusion of CM31; output coordinates use its exact codec. -/
theorem decodePoint_of_assembled (limbs : List Nat) (parameter : QM31Exact)
    (assembled : assemble limbs = some parameter) :
    decodePoint limbs = exactSecureCirclePointFromDecoded parameter := by
  simp only [decodePoint, assembled, Option.bind_some]

def first (tape : Tape) (s : Transcript) := circle decodePoint tape 3 s
def firstScript (digest : Block) := circleScript decodePoint 3 digest

theorem first_script_exact (tape : Tape) (s : Transcript) :
    run tape (firstScript s.digest) s.oracle =
      (some ((first tape s).1, (first tape s).2.digest), (first tape s).2.oracle) :=
  run_circle decodePoint tape 3 s

-- Equality of the two encoded coordinates is extensional equality of their
-- 32 literal bytes. No caller-supplied comparison function is involved.
local instance : DecidableEq SecureCirclePointBytes := Classical.decEq _

def second (point : SecureCirclePointBytes) (tape : Tape) (s : Transcript) :=
  distinct decodePoint point tape 3 s
def secondScript (point : SecureCirclePointBytes) (digest : Block) :=
  distinctScript decodePoint point 3 digest

theorem second_script_exact (point : SecureCirclePointBytes) (tape : Tape) (s : Transcript) :
    run tape (secondScript point s.digest) s.oracle =
      (some ((second point tape s).1, (second point tape s).2.digest),
        (second point tape s).2.oracle) :=
  run_distinct decodePoint point tape 3 s

theorem second_success_distinct (point result : SecureCirclePointBytes)
    (tape : Tape) (s : Transcript) (success : (second point tape s).1 = .ok result) :
    result ≠ point := distinct_success_ne decodePoint point tape 3 s result success

/- The sampler's canonical-limb seam is discharged by challenge_assembles. These
theorems do NOT sample independently on a cache hit and do NOT assert that
actual source states are freshly exposed at OOD boundaries. The ROM lift must
construct that coupling (or charge the exact premature/collision events).
No probability, Rust extraction or full semantic execution is claimed here. -/
#print axioms decodePoint_of_assembled
#print axioms challenge_assembles
#print axioms first_script_exact
#print axioms second_script_exact
#print axioms second_success_distinct
end
end AspisV8Completion.FSV7OODSampler
