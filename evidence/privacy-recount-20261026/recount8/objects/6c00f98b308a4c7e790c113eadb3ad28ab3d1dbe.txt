import R1Z.ProverCommitRows29
import R1Z.ProverCommitInit28
/-! P6 iteration assembly, then both circle points and the complete Transcript
suffix. This file does not assert a retry/serialization or whole-game join. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitWalk29
open Aeneas Aeneas.Std Result ProverCommitStateLift28 ProverCommitWalk28

def suffix {M : Type → Type} [Monad M] [MonadLiftT Result M]
    (effect : Unit → Parts → M ProverCommitWalk28.Bytes32)
    (sample : core.result.Result ProverCommitStep29.Values AspisR1SimSemantic20.r1_wire.Error)
    (state : SemanticState) (records : Records)
    (variant : AspisR1SimControl21.transport.Variant) : M Outcome := do
  match sample with
  | .Err _ => pure (rejected state.state)
  | .Ok sem =>
    let record0 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (alloc.vec.Vec U8))
      records.semantic 25#usize
    let record0 ← alloc.vec.CloneVec.clone core.clone.CloneU8 record0
    let (sample0,state0) ← ProverCommitCircleProgram28.point effect ProverCommitCircle25.policy
      (ProverCommitCircle25.fromSemantic state) 25#u8 record0
    match sample0 with
    | .Err _ => pure (rejected state0.state)
    | .Ok z0 =>
      let record1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (alloc.vec.Vec U8))
        records.semantic 26#usize
      let record1 ← alloc.vec.CloneVec.clone core.clone.CloneU8 record1
      let (sample1,state1) ← ProverCommitCircleProgram28.point effect ProverCommitCircle25.policy
        state0 26#u8 record1
      match sample1 with
      | .Err _ => pure (rejected state1.state)
      | .Ok z1 =>
        ProverCommitControlProgram28.tail effect ProverCommitQuery26.policy () state1.state
          (mapArray fromSemantic sem)
          (Array.make 2#usize [mapArray fromCircle z0,mapArray fromCircle z1]) records variant


def continuation {M : Type → Type} [Monad M] [MonadLiftT Result M]
    (effect : Unit → Parts → M ProverCommitWalk28.Bytes32) (initial : SemanticState)
    (records : Records) (variant : AspisR1SimControl21.transport.Variant) :
    M (core.result.Result Output AspisR1SimControl21.verifier.Error) := do
  let result ← ProverCommitRows29.rows effect records.semantic 0#usize 25 initial
    (Array.repeat 25#usize AspisR1SimSemantic20.aspis_core.field.QM31.ZERO)
  match result with
  | .Err e => pure (.Err e)
  | .Ok (state,sem) => do
    let out ← suffix effect (.Ok sem) state records variant
    pure out.1

theorem suffix_source {M : Type → Type} [Monad M] [MonadLiftT Result M]
    (effect : Unit → Parts → M ProverCommitWalk28.Bytes32) (initial : SemanticState)
    (records : Records) (variant : AspisR1SimControl21.transport.Variant) :
    ProverCommitWalk28.continuation effect initial records variant =
    (do let (sample,state) ← ProverCommitSemanticRows28.rows effect records.semantic 0#usize 25 initial
          (Array.repeat 25#usize AspisR1SimSemantic20.aspis_core.field.QM31.ZERO)
        suffix effect sample state records variant) := by rfl

/-- Composes the finite row induction with both circle points and every
Transcript suffix operation. Only the locally discarded error state is forgotten. -/
theorem continuation_model {M : Type → Type} [Monad M] [LawfulMonad M]
    [MonadLiftT Result M] [LawfulMonadLiftT Result M]
    (effect : Unit → Parts → M ProverCommitWalk28.Bytes32) (initial : SemanticState)
    (records : Records) (variant : AspisR1SimControl21.transport.Variant) :
    continuation effect initial records variant =
    (do let out ← ProverCommitWalk28.continuation effect initial records variant
        pure out.1) := by
  unfold continuation
  rw [ProverCommitRows29.rows_model effect records.semantic 0#usize 25 initial _ (by decide)]
  rw [suffix_source]
  simp only [bind_assoc]
  apply ProverCommitRows29.bind_same
  intro result
  rcases result with ⟨sample,state⟩
  cases sample with
  | Err e => simp only [ProverCommitStep29.discard,pure_bind,suffix,rejected]
  | Ok sem => simp only [ProverCommitStep29.discard,pure_bind]

def walk {M : Type → Type} [Monad M] [MonadLiftT Result M]
    (effect : Unit → Parts → M ProverCommitWalk28.Bytes32) (publicBytes : Slice U8)
    (records : Records) (variant : AspisR1SimControl21.transport.Variant) :
    M (core.result.Result Output AspisR1SimControl21.verifier.Error) := do
  let initial ← ProverCommitInit28.start effect () publicBytes records.c1_root
  match initial with
  | .Err _ => pure (.Err .Semantic)
  | .Ok initial => continuation effect ⟨initial.state,(),initial.next_row⟩ records variant

theorem walk_model {M : Type → Type} [Monad M] [LawfulMonad M]
    [MonadLiftT Result M] [LawfulMonadLiftT Result M]
    (effect : Unit → Parts → M ProverCommitWalk28.Bytes32) (publicBytes : Slice U8)
    (records : Records) (variant : AspisR1SimControl21.transport.Variant) :
    walk effect publicBytes records variant =
    (do let out ← ProverCommitInit28.walk effect publicBytes records variant
        pure out.1) := by
  simp only [walk,ProverCommitInit28.walk,bind_assoc]
  apply ProverCommitRows29.bind_same
  intro initial
  cases initial with
  | Err e => simp only [pure_bind,rejected]
  | Ok initial => exact continuation_model effect _ records variant

/-- The composed P6 owner equality retains final native machine and ordered
history when instantiated with the actual extracted oracle. -/
theorem logged_model (publicBytes : Slice U8) (records : Records)
    (variant : AspisR1SimControl21.transport.Variant)
    (machine : ProverCommitLogged28.LoggedMachine) :
    walk (ProverCommitLogged28.dictionary ProverCommitControl28.extracted)
      publicBytes records variant machine =
    (do let out ← ProverCommitInit28.walk
          (ProverCommitLogged28.dictionary ProverCommitControl28.extracted)
          publicBytes records variant
        pure out.1) machine := by
  exact congrFun (walk_model (M := Port ProverCommitLogged28.LoggedMachine)
    (ProverCommitLogged28.dictionary ProverCommitControl28.extracted)
    publicBytes records variant) machine

theorem walk_effects (publicBytes : Slice U8) (records : Records)
    (variant : AspisR1SimControl21.transport.Variant)
    (machine : ProverCommitLogged28.LoggedMachine) :
    walk (ProverCommitLogged28.dictionary ProverCommitControl28.extracted)
      publicBytes records variant machine =
    walk (ProverCommitLogged28.dictionary ProverCommitControl28.reference)
      publicBytes records variant machine := by
  exact install _ _ (ProverCommitLogged28.logged_exact _ _ ProverCommitCoinCall27.call_exact)
    (fun e => walk (fun (_ : Unit) p => read e p) publicBytes records variant) machine

#print axioms suffix_source
#print axioms continuation_model
#print axioms walk_model
#print axioms logged_model
#print axioms walk_effects
end R1Z.ProverCommitWalk29
