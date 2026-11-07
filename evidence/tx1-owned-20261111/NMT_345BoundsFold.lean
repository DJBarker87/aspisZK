import NMT_345SplitLength
import NMT_345SplitStart
import NMT_345SplitChecked
import NMT_345SumStep
import NMT_345TailFold
import NMT_345TryCongr
import NMT_CallTree
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result

def boundsFold {W : Type} (c : Calls) (s : ProofData W) : Result Ret := do
 let length ← c.c4
 let start ← c.c8
 let sum ← lift (Usize.checked_add start length)
 tryStep (NMT_stage1_owned.core.option.Option.ok_or sum NMT_stage1_owned.solana_program_error.ProgramError.InvalidAccountData)
  (fun end_ => tailFold c ⟨s,start,end_⟩)

theorem bounds_fold {W : Type} (c : Calls) (s : ProofData W) : raw10 c s = boundsFold c s := by
 unfold boundsFold
 rw [length_call]
 apply AspisR1.NMT_CallTree.result_congr
 intro length
 rw [start_call]
 apply AspisR1.NMT_CallTree.result_congr
 intro start
 rw [checked_call]
 apply AspisR1.NMT_CallTree.result_congr
 intro sum
 rw [sum_call]
 apply try_congr
 intro end_
 exact tail_fold _ _
#print axioms bounds_fold
end NMT_345
