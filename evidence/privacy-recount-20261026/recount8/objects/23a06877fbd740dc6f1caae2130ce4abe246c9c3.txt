import R1Z.ProverCommitEffectCallers27
/-! State transformer used by the complete continuation port. Result failures
and divergence propagate; verifier errors remain ordinary values and retain
state. Pure instructions do not reset the threaded oracle state. -/
set_option autoImplicit false
namespace R1Z.ProverCommitStateLift28
open Aeneas Aeneas.Std Result
abbrev Port (S A : Type) := StateT S Result A
abbrev Parts := ProverCommitOracleEffect26.Parts
abbrev Bytes32 := ProverCommitCoinCall27.Bytes32
abbrev Effect (S : Type) := S → Parts → Result (Bytes32 × S)

def read {S : Type} (effect : Effect S) (parts : Parts) : Port S Bytes32 :=
  fun state => effect state parts

def liftResult {S A : Type} (r : Result A) : Port S A :=
  fun state => do let value ← r; ok (value,state)

/-- The single state-threading equation: every continuation receives exactly
its predecessor's returned state, including when the value is a verifier error. -/
theorem bind_run {S A B : Type} (p : Port S A) (k : A → Port S B) (state : S) :
    (p >>= k) state = (do let (value,next) ← p state; k value next) := by rfl

theorem lift_run {S A : Type} (r : Result A) (state : S) :
    liftResult r state = (do let value ← r; ok (value,state)) := by rfl

theorem read_run {S : Type} (effect : Effect S) (parts : Parts) (state : S) :
    read effect parts state = effect state parts := by rfl

/-- A pointwise implementation equation may be installed in every stateful
continuation, rather than separately unfolding every caller's hash operations. -/
theorem install {S A : Type} (actual expected : Effect S)
    (calls : ∀ state parts, actual state parts = expected state parts)
    (continuation : Effect S → Port S A) (state : S) :
    continuation actual state = continuation expected state := by
  have eq : actual = expected := funext fun s => funext fun p => calls s p
  rw [eq]

#print axioms bind_run
#print axioms lift_run
#print axioms read_run
#print axioms install
end R1Z.ProverCommitStateLift28
