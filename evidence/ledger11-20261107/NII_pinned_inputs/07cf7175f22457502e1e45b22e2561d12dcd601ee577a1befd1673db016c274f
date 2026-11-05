import NGL_MapReference.Funs
import NGL_ErrorCarrier
import NGL_FirstDecoded
set_option autoImplicit false
namespace NGL_MapReferenceModel
open Aeneas Aeneas.Std Result
abbrev E := AdapterRw.aspis_r1_cost_probe.verifier.Error
abbrev V := alloc.vec.Vec U8

def error : E → NGL_MapReference.VerifierError
  | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
  | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
  | .Checkpoint => .Checkpoint | .Allocation => .Allocation

def input : core.result.Result V E → core.result.Result V NGL_MapReference.VerifierError
  | .Ok v => .Ok v | .Err e => .Err (error e)

def output : core.result.Result V NGL_MapReference.ProgramError →
    core.result.Result V AdapterRw.solana_program_error.ProgramError
  | .Ok v => .Ok v | .Err e => .Err (NGL_ErrorCarrier.from_mapped e)

theorem source (r : core.result.Result V E) :
    (do let observed ← NGL_MapReference.map_ref (input r); ok (output observed)) =
      ok (NGL_FirstDecoded.mapped r) := by
  cases r with
  | Ok v => rfl
  | Err e => cases e <;> rfl
#print axioms source
end NGL_MapReferenceModel
