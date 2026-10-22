import R1Z.ProverCommitSemanticRows28
import R1Z.ProverCommitLogged28
import R1Z.ProverCommitCircle25
/-! Effectful walk continuation after SemanticTranscript::new. All validators,
scalar/circle/query policies are concrete. The initialization and native outer
owner are deliberately not asserted by the following execution equation. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitWalk28
open Aeneas Aeneas.Std Result ProverCommitStateLift28
abbrev Bytes32 := ProverCommitCoinCall27.Bytes32
abbrev SK := AspisR1SimSemantic20.aspis_core.field.QM31
abbrev CK := AspisR1CircleCaller25.aspis_core.field.QM31
abbrev K := AspisR1SimControl21.aspis_core.field.QM31
abbrev SemanticState := ProverCommitSemanticRows28.State Unit
abbrev Records := AspisR1SimControl21.sim.Records
abbrev Trace := alloc.vec.Vec (U16 × Usize × AspisR1SimControl21.aspis_core.field.wide_exact.WideExact)
abbrev Output := ProverCommitControl28.Values × ProverCommitControl28.Points ×
  AspisR1SimControl21.aspis_core.field.wide_exact.WideExact ×
  AspisR1SimControl21.aspis_core.field.wide_exact.WideExact ×
  AspisR1SimControl21.aspis_core.field.wide_exact.WideExact ×
  AspisR1SimControl21.aspis_core.field.wide_exact.WideExact × Array U32 22#usize × K
abbrev Outcome := (core.result.Result Output AspisR1SimControl21.verifier.Error) × Bytes32 × Trace

def fromSemantic (q : SK) : K := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def fromCircle (q : CK) : K := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def mapArray {A B : Type} {n : Usize} (f : A → B) (xs : Array A n) : Array B n :=
  ⟨xs.val.map f,by simpa only [List.length_map] using xs.property⟩

def rejected (state : Bytes32) : Outcome :=
  (.Err .Semantic,state,alloc.vec.Vec.new _)

/-- The 25 semantic rows, both circle rows, suffix initialization, scalar
policies, query scanner and rho share one mutable machine. -/
def continuation {M : Type → Type} [Monad M] [MonadLiftT Result M]
    (effect : Unit → Parts → M Bytes32) (initial : SemanticState)
    (records : Records) (variant : AspisR1SimControl21.transport.Variant) : M Outcome := do
  let (sample,state) ← ProverCommitSemanticRows28.rows effect records.semantic 0#usize 25 initial
    (Array.repeat 25#usize AspisR1SimSemantic20.aspis_core.field.QM31.ZERO)
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

/-- Complete continuation value, final machine and repeated ordered reads
agree with the concrete reference; no policy or execution-join premise. -/
theorem continuation_effects (initial : SemanticState) (records : Records)
    (variant : AspisR1SimControl21.transport.Variant)
    (machine : ProverCommitLogged28.LoggedMachine) :
    continuation (ProverCommitLogged28.dictionary ProverCommitControl28.extracted)
      initial records variant machine =
    continuation (ProverCommitLogged28.dictionary ProverCommitControl28.reference)
      initial records variant machine := by
  exact install _ _ (ProverCommitLogged28.logged_exact _ _ ProverCommitCoinCall27.call_exact)
    (fun e => continuation (fun (_ : Unit) p => read e p) initial records variant) machine

#print axioms continuation_effects
end R1Z.ProverCommitWalk28
