import NMT_345AdmittedFold
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result NMT_stage1_owned
/-- Source-only fold of the exact E003 body. Calls remain uninterpreted here;
concrete call observations and all allocation/error prefixes are separate
obligations. This theorem is deliberately NOT a candidate row root. -/
def sourceFold {W : Type} (c : Calls) (s : Parent W) : Result Ret := do
 let firstRoute ← c.c1 core.cmp.PartialEqU8 s.data (Array.make 2#usize [3#u8,10#u8])
 if firstRoute then admittedFold c s else do
  let secondRoute ← c.c1 core.cmp.PartialEqU8 s.data (Array.make 2#usize [3#u8,11#u8])
  if secondRoute then admittedFold c s else .ok (.Err .InvalidInstructionData)

theorem source_fold {W : Type} (c : Calls) (s : Parent W) :
 emitted c s = sourceFold c s := by
 rw [emitted_route10]
 unfold route10 sourceFold
 apply AspisR1.NMT_CallTree.result_congr
 intro firstRoute
 cases firstRoute with
 | true => exact admitted_fold c s
 | false =>
  apply AspisR1.NMT_CallTree.result_congr
  intro secondRoute
  cases secondRoute with
  | true => exact admitted_fold c s
  | false => rfl
#print axioms source_fold
end NMT_345
