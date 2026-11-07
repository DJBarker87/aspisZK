import NMT_R2_ResultTry
import NMT_345BoundsFold
set_option autoImplicit false
noncomputable section
namespace NMT_R2_BoundsPacket
open Aeneas Aeneas.Std NMT_345

def bounds {W : Type} (c : Calls) (s : ProofData W) : Result (core.result.Result (Bounds W) PE) := do
 let length ← c.c4
 let start ← c.c8
 let sum ← lift (Usize.checked_add start length)
 NMT_R2_ResultTry.bind
  (NMT_stage1_owned.core.option.Option.ok_or sum NMT_stage1_owned.solana_program_error.ProgramError.InvalidAccountData)
  (fun end_ => NMT_R2_ResultTry.pure ⟨s,start,end_⟩)

theorem source {W : Type} (c : Calls) (s : ProofData W) :
 NMT_R2_ResultTry.bind (bounds c s) (tailFold c) = boundsFold c s := by
 simp only [bounds,Bind.bind,NMT_R2_ResultTry.outer,NMT_R2_ResultTry.assoc,NMT_R2_ResultTry.pure_left]
 rfl
#print axioms source
end NMT_R2_BoundsPacket
end
