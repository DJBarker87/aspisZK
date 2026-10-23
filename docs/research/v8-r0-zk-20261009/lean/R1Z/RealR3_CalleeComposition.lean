import R1Z.RealR3_SemanticEmission
/-! Contextual composition for the separately certified semantic callee.
The pointwise premise includes the entire returned machine, including ordered
hash effects. Native caller evidence is external Kani evidence; this module
is not itself an interpreter or a concrete real-experiment certificate. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.RealR3_CalleeComposition
open Aeneas Aeneas.Std Result ProverCommitStateLift28 RealR3_SemanticEmission
abbrev Callee (S : Type) := State → U8 → Bytes → Port S (ScalarResult × State)

def emitWith {S : Type} (callee : Callee S) (state : State) (row : U8)
    (framed : Bytes) (outputPrefix : List U8) : Port S (ScalarResult × State × List U8) := do
  let (value,next) ← callee state row framed
  match value with
  | .Err e => pure (.Err e,next,outputPrefix)
  | .Ok q => pure (.Ok q,next,outputPrefix ++ framed.val)

theorem callee_transport {S : Type} (left right : Callee S)
    (same : ∀ s r f m, left s r f m = right s r f m)
    (state : State) (row : U8) (frame : Bytes) (outputPrefix : List U8) (machine : S) :
    emitWith left state row frame outputPrefix machine =
      emitWith right state row frame outputPrefix machine := by
  simp only [emitWith,bind_run,same]

def rowsWith {S : Type} (callee : Callee S) :
    List (U8 × Bytes) → State → List U8 → Port S (RowsResult × State × List U8)
  | [],state,outputPrefix => pure (.Ok (),state,outputPrefix)
  | (row,frame)::tail,state,outputPrefix => do
    let (value,next,bytes) ← emitWith callee state row frame outputPrefix
    match value with
    | .Err e => pure (.Err e,next,bytes)
    | .Ok _ => rowsWith callee tail next bytes

theorem rows_transport {S : Type} (left right : Callee S)
    (same : ∀ s r f m, left s r f m = right s r f m)
    (frames : List (U8 × Bytes)) (state : State) (outputPrefix : List U8) (machine : S) :
    rowsWith left frames state outputPrefix machine =
      rowsWith right frames state outputPrefix machine := by
  have eq : left = right := funext fun s => funext fun r => funext fun f => funext fun m => same s r f m
  rw [eq]

theorem semantic_install {S : Type} (effect : Unit → Parts → Port S Bytes32)
    (frames : List (U8 × Bytes)) (state : State) (outputPrefix : List U8) (machine : S) :
    rowsWith (ProverCommitSemanticProgram28.semantic effect) frames state outputPrefix machine =
      rows effect frames state outputPrefix machine := by
  induction frames generalizing state outputPrefix machine with
  | nil => rfl
  | cons frame tail ih =>
    rcases frame with ⟨row,framed⟩
    simp only [rowsWith,rows,emitWith,emit,bind_run]
    cases called : ProverCommitSemanticProgram28.semantic effect state row framed machine with
    | fail e => rfl
    | div => rfl
    | ok out =>
      rcases out with ⟨⟨value,next⟩,after⟩
      cases value with
      | Err e => rfl
      | Ok q => exact ih next (outputPrefix ++ framed.val) after

#print axioms callee_transport
#print axioms rows_transport
#print axioms semantic_install
end R1Z.RealR3_CalleeComposition
