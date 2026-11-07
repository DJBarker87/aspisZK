import NMT_345StepBase
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
structure Selected (W : Type) extends Parent W where
 proofAccount : Account
 publicAccount : Account
 checkpointAccount : Account
/-- Three exact SDK-free slice reads in E003 source order; original parent
and the full world stay in the same record. -/
def select {W : Type} (s : Parent W) (next : Selected W → Result Ret) : Result Ret := do
 let p ← Slice.index_usize s.accounts 0#usize
 let pub ← Slice.index_usize s.accounts 1#usize
 let ck ← Slice.index_usize s.accounts 2#usize
 next ⟨s,p,pub,ck⟩
/-- First read occurs before the public/checkpoint reads, with all outer
fail/div propagation unchanged. The suffix is an arbitrary continuation. -/
theorem select_first {W : Type} (s : Parent W) (next : Selected W → Result Ret) :
 select s next = (Slice.index_usize s.accounts 0#usize >>= fun p => do
  let pub ← Slice.index_usize s.accounts 1#usize
  let ck ← Slice.index_usize s.accounts 2#usize
  next ⟨s,p,pub,ck⟩) := rfl

theorem selected_original {W : Type} (s : Parent W) (p pub ck : Account) :
 (Selected.mk s p pub ck).toParent = s := rfl
#print axioms select_first
#print axioms selected_original
end NMT_345
