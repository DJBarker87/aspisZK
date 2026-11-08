import NNG_TreeTail345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Tree345
open Aeneas Aeneas.Std Result NMT_345 NMT_CallTree

def selected {W : Type} (c : Calls) (s : Selected W) : Code Ret :=
 NNG_TreeBase345.prelude c s (fun d=>NNG_TreeBase345.middle c d (NNG_TreeTail345.bounds c))
def select {W : Type} (c : Calls) (s : Parent W) : Code Ret := do
 let p ← (liftM (Slice.index_usize s.accounts 0#usize) : Code _)
 let pub ← (liftM (Slice.index_usize s.accounts 1#usize) : Code _)
 let ck ← (liftM (Slice.index_usize s.accounts 2#usize) : Code _)
 selected c ⟨s,p,pub,ck⟩
def admitted {W : Type} (c : Calls) (s : Parent W) : Code Ret :=
 if Slice.len s.accounts !=3#usize then pure (.Err .InvalidInstructionData) else select c s

def tree {W : Type} (c : Calls) (s : Parent W) : Code Ret := do
 let firstRoute ← (liftM (c.c1 Aeneas.Std.core.cmp.PartialEqU8 s.data (Array.make 2#usize [3#u8,10#u8])) : Code _)
 if firstRoute then admitted c s else do
  let secondRoute ← (liftM (c.c1 Aeneas.Std.core.cmp.PartialEqU8 s.data (Array.make 2#usize [3#u8,11#u8])) : Code _)
  if secondRoute then admitted c s else pure (.Err .InvalidInstructionData)

theorem erase_selected {W : Type} (c : Calls) (s : Selected W) : erase (selected c s)=selectedFold c s := by
 unfold selected selectedFold
 rw [NNG_TreeBase345.erase_prelude]
 -- Congruence is through the complete already-checked prelude.
 change prefixFold c s (fun d=>erase (NNG_TreeBase345.middle c d (NNG_TreeTail345.bounds c)))=prefixFold c s _
 exact prefix_congr c s _ _ (fun d=>by rw [NNG_TreeBase345.erase_middle];exact middle_congr c d _ _ (NNG_TreeTail345.erase_bounds c))
#print axioms erase_selected

theorem erase_select {W : Type} (c : Calls) (s : Parent W) :
 erase (select c s)=NMT_345.select s (selectedFold c) := by
 unfold select NMT_345.select
 simp only [Bind.bind,erase_bind,erase_lift,erase_selected]
#print axioms erase_select

theorem erase_admitted {W : Type} (c : Calls) (s : Parent W) : erase (admitted c s)=admittedFold c s := by
 unfold admitted admittedFold
 split
 · rfl
 · exact erase_select c s
#print axioms erase_admitted

theorem source {W : Type} (c : Calls) (s : Parent W) : erase (tree c s)=emitted c s := by
 rw [NMT_345.source_fold]
 unfold tree sourceFold
 simp only [Bind.bind,erase_bind,erase_lift]
 apply result_congr
 intro firstRoute
 cases firstRoute with
 | true=>exact erase_admitted c s
 | false=>
  apply result_congr
  intro secondRoute
  cases secondRoute with
  | true=>exact erase_admitted c s
  | false=>rfl
#print axioms source
end AspisR1.NNG_Tree345
