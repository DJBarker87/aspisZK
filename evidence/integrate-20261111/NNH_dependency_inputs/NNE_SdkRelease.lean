import NNE_SdkAcquire
set_option autoImplicit false
namespace NNE_SdkRelease
open RSL
def next (s : SdkState) (a : AccountInfo) (t : Nat) : Kind → SdkState
 | .shared => s.put a.cell {(s.cells a.cell) with readers := (s.cells a.cell).readers.erase t}
 | .exclusive => s.put a.cell {(s.cells a.cell) with writer := none}

theorem relation (s : SdkState) (a : AccountInfo) (t : Nat) (k : Kind)
 (env : Env) (o : Obs SdkState) :
 release a t k s env o ↔ o = ⟨.ret (next s a t k),[.release a.cell t k]⟩ := by
 cases k <;> simp [release,next,Spec.bind,Spec.emit,Spec.pure]

theorem sdk_release (accounts : Nat → NLF_SdkModel.Account) (money : Nat → Nat)
 (s : SdkState) (a : AccountInfo) (t : Nat) (k : Kind)
 (live : NLF_RefCell.live (NNE_SdkState.cell money s a.cell) t (NNE_SdkCells.kind k)) :
 NLF_SdkModel.release (NNE_SdkState.state accounts money s) ⟨a.cell,t,NNE_SdkCells.kind k⟩ =
 .ok (NNE_SdkState.state accounts money (next s a t k)) := by
 cases k with
 | shared =>
  change (s.cells a.cell).writer = none ∧ t ∈ (s.cells a.cell).readers at live
  simp only [NLF_SdkModel.release,NNE_SdkCells.kind,NNE_SdkState.state,
   NLF_RefCell.dropShared,NNE_SdkState.cell,live.1,live.2,and_self,ite_true]
  simp only [next,NLF_SdkModel.put]
  apply congrArg Except.ok
  congr 1
  funext j
  by_cases hj : j = a.cell
  · subst j; simp [NNE_SdkState.cell,RSL.SdkState.put,live]
  · simp [NNE_SdkState.cell,RSL.SdkState.put,hj]
 | exclusive =>
  change (s.cells a.cell).writer = some t at live
  simp only [NLF_SdkModel.release,NNE_SdkCells.kind,NNE_SdkState.state,
   NLF_RefCell.dropExclusive,NNE_SdkState.cell,live,ite_true]
  simp only [next,NLF_SdkModel.put]
  apply congrArg Except.ok
  congr 1
  funext j
  by_cases hj : j = a.cell
  · subst j; simp [NNE_SdkState.cell,RSL.SdkState.put,live]
  · simp [NNE_SdkState.cell,RSL.SdkState.put,hj]
#print axioms relation
#print axioms sdk_release
end NNE_SdkRelease
