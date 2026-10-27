import R1Z.ProverCommitWalk29
/-! Range-based source owner after the independently checked native iteration
substitution. The Rust/Kani evidence is an external source boundary, not an
axiom in Lean. This module composes the finite native counter with the retained
owned walk and stateful model, including ordered oracle effects on rejection. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitNative30
open Aeneas Aeneas.Std Result ProverCommitStateLift28 ProverCommitWalk28

def continuation {M : Type → Type} [Monad M] [MonadLiftT Result M]
    (effect : Unit → Parts → M ProverCommitWalk28.Bytes32) (initial : SemanticState)
    (records : Records) (variant : AspisR1SimControl21.transport.Variant) :
    M (core.result.Result Output AspisR1SimControl21.verifier.Error) := do
  let result ← ProverCommitRows29.rangeRows effect records.semantic 0#u8 25 initial
    (Array.repeat 25#usize AspisR1SimSemantic20.aspis_core.field.QM31.ZERO)
  match result with
  | .Err e => pure (.Err e)
  | .Ok (state,sem) => do
    let out ← ProverCommitWalk29.suffix effect (.Ok sem) state records variant
    pure out.1

theorem continuation_owned {M : Type → Type} [Monad M] [LawfulMonad M]
    [MonadLiftT Result M] [LawfulMonadLiftT Result M]
    (effect : Unit → Parts → M ProverCommitWalk28.Bytes32) (initial : SemanticState)
    (records : Records) (variant : AspisR1SimControl21.transport.Variant) :
    continuation effect initial records variant =
    ProverCommitWalk29.continuation effect initial records variant := by
  unfold continuation ProverCommitWalk29.continuation
  rw [ProverCommitRows29.range_model effect records.semantic 0#u8 25 initial _ (by decide)]
  have zero : UScalar.cast .Usize (0#u8) = 0#usize := by scalar_tac
  rw [zero]
  rfl

def walk {M : Type → Type} [Monad M] [MonadLiftT Result M]
    (effect : Unit → Parts → M ProverCommitWalk28.Bytes32) (publicBytes : Slice U8)
    (records : Records) (variant : AspisR1SimControl21.transport.Variant) :
    M (core.result.Result Output AspisR1SimControl21.verifier.Error) := do
  let initial ← ProverCommitInit28.start effect () publicBytes records.c1_root
  match initial with
  | .Err _ => pure (.Err .Semantic)
  | .Ok initial => continuation effect ⟨initial.state,(),initial.next_row⟩ records variant

theorem walk_owned {M : Type → Type} [Monad M] [LawfulMonad M]
    [MonadLiftT Result M] [LawfulMonadLiftT Result M]
    (effect : Unit → Parts → M ProverCommitWalk28.Bytes32) (publicBytes : Slice U8)
    (records : Records) (variant : AspisR1SimControl21.transport.Variant) :
    walk effect publicBytes records variant =
    ProverCommitWalk29.walk effect publicBytes records variant := by
  simp only [walk,ProverCommitWalk29.walk,continuation_owned]
  rfl

theorem walk_model {M : Type → Type} [Monad M] [LawfulMonad M]
    [MonadLiftT Result M] [LawfulMonadLiftT Result M]
    (effect : Unit → Parts → M ProverCommitWalk28.Bytes32) (publicBytes : Slice U8)
    (records : Records) (variant : AspisR1SimControl21.transport.Variant) :
    walk effect publicBytes records variant =
    (do let out ← ProverCommitInit28.walk effect publicBytes records variant
        pure out.1) := by
  rw [walk_owned]
  exact ProverCommitWalk29.walk_model effect publicBytes records variant

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

#print axioms continuation_owned
#print axioms walk_owned
#print axioms walk_model
#print axioms logged_model
end R1Z.ProverCommitNative30
