import R1Z.ProverCommitStepSource29
import R1Z.ProverCommitSemanticRows28
/-! P6 one-step continuation. Errors leave the external machine observable,
while the local owned semantic transcript is discarded by the Rust `?`. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitStep29
open Aeneas Aeneas.Std Result AspisR1SimSemantic20 ProverCommitStateLift28
abbrev Error := AspisR1SimControl21.verifier.Error
abbrev State (H : Type) := ProverCommitSemanticRows28.State H
abbrev Values := ProverCommitSemanticRows28.Values
abbrev Records := ProverCommitSemanticRows28.Records
abbrev Output (H : Type) := core.result.Result (State H × Values) Error

def discard {H : Type} (result : core.result.Result Values r1_wire.Error × State H) : Output H :=
  match result with
  | (.Err _,_) => .Err .Semantic
  | (.Ok sem,state) => .Ok (state,sem)

def iteration {M : Type → Type} [Monad M] [MonadLiftT Result M] {H : Type}
    (effect : H → Parts → M Bytes32) (state : State H) (row : U8)
    (record : alloc.vec.Vec U8) (sem : Values) : M (Output H) := do
  let (value,next) ← ProverCommitSemanticProgram28.semantic effect state row record
  match value with
  | .Err _ => pure (.Err .Semantic)
  | .Ok value => do
    let index ← lift (UScalar.cast .Usize row)
    let sem ← Array.update sem index value
    pure (.Ok (next,sem))

/-- The signed and unsigned extracted numeral annotations have identical
shift semantics; the source integer is the same small positive constant. -/
theorem shift_count : (32#i32).val = Int.ofNat (32#u32).val := by decide

/-- Pure specialization reconstructs the actual extracted owned step. -/
theorem extracted_step {H : Type} (hash : aspis_core.digest.Digest32 H)
    (state : State H) (row : U8) (record : alloc.vec.Vec U8) (sem : Values) :
    sim.owned29.semantic_step hash state row record sem =
    iteration hash.digest state row record sem := by
  unfold sim.owned29.semantic_step iteration
  rw [← ProverCommitSemanticSource28.semantic]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro v hv
  rcases v with ⟨value,next⟩
  cases value <;> rfl

/-- Install the same concrete oracle machine including errors and read order. -/
theorem iteration_effects (state : State Unit) (row : U8) (record : alloc.vec.Vec U8)
    (sem : Values) (machine : ProverCommitCoinCall27.Machine) :
    iteration (ProverCommitControl28.dictionary ProverCommitControl28.extracted)
      state row record sem machine =
    iteration (ProverCommitControl28.dictionary ProverCommitControl28.reference)
      state row record sem machine := by
  exact install _ _ ProverCommitCoinCall27.call_exact
    (fun e => iteration (ProverCommitControl28.dictionary e) state row record sem) machine

def selectedIteration {M : Type → Type} [Monad M] [MonadLiftT Result M] {H : Type}
    (effect : H → Parts → M Bytes32) (state : State H) (row : U8)
    (records : Records) (sem : Values) : M (Output H) := do
  let index ← lift (UScalar.cast .Usize row)
  let record ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (alloc.vec.Vec U8)) records index
  let record ← alloc.vec.CloneVec.clone core.clone.CloneU8 record
  iteration effect state row record sem

/-- Includes native record selection and its index failure, before the
semantic call, `?` exit and selected array write. -/
theorem extracted_selected {H : Type} (hash : aspis_core.digest.Digest32 H)
    (state : State H) (row : U8) (records : Records) (sem : Values) :
    sim.owned29.iteration hash state row records sem =
    selectedIteration hash.digest state row records sem := by
  unfold sim.owned29.iteration selectedIteration
  simp only [← extracted_step,liftM,monadLift_self]

theorem selected_effects (state : State Unit) (row : U8) (records : Records)
    (sem : Values) (machine : ProverCommitCoinCall27.Machine) :
    selectedIteration (ProverCommitControl28.dictionary ProverCommitControl28.extracted)
      state row records sem machine =
    selectedIteration (ProverCommitControl28.dictionary ProverCommitControl28.reference)
      state row records sem machine := by
  exact install _ _ ProverCommitCoinCall27.call_exact
    (fun e => selectedIteration (ProverCommitControl28.dictionary e) state row records sem) machine

#print axioms shift_count
#print axioms extracted_step
#print axioms iteration_effects
#print axioms extracted_selected
#print axioms selected_effects
end R1Z.ProverCommitStep29
