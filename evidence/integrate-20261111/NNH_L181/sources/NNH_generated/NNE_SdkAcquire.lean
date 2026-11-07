import NNE_SdkState
set_option autoImplicit false
namespace NNE_SdkAcquire
open RSL
def allowed (s : SdkState) (a : AccountInfo) : Kind → Bool
 | .shared => sharedOk (s.cells a.cell)
 | .exclusive => exclusiveOk (s.cells a.cell)
def next (s : SdkState) (a : AccountInfo) (k : Kind) : SdkState :=
 if allowed s a k then
  let c := s.cells a.cell
  let c' := match k with
   | .shared => {c with readers := s.next :: c.readers}
   | .exclusive => {c with writer := some s.next}
  {(s.put a.cell c') with next := s.next+1}
 else {s with next := s.next+1}
def reply (s : SdkState) (a : AccountInfo) (k : Kind) : Except ProgramError Nat :=
 if allowed s a k then .ok s.next else .error .accountBorrowFailed

theorem relation (s : SdkState) (a : AccountInfo) (k : Kind) (env : Env)
 (o : Obs (Except ProgramError Nat × SdkState)) :
 acquire a k s env o ↔
 o = ⟨.ret (reply s a k,next s a k),[.acquire a.cell s.next k (allowed s a k)]⟩ := by
 cases k <;> unfold acquire <;> simp only <;> split <;>
 simp_all [reply,next,allowed,Spec.bind,Spec.emit,Spec.pure]

def sdkReply (a : AccountInfo) (k : Kind) : Except ProgramError Nat →
 Except NLF_SdkModel.ProgramError NLF_RefCell.Guard
 | .ok t => .ok ⟨a.cell,t,NNE_SdkCells.kind k⟩
 | .error _ => .error .accountBorrowFailed

theorem sdk_wrap (accounts : Nat → NLF_SdkModel.Account) (money : Nat → Nat)
 (s : SdkState) (a : AccountInfo) (k : Kind) (fresh : NNE_SdkState.Fresh s) :
 NLF_SdkModel.wrap (NNE_SdkState.state accounts money s) a.cell s.next (NNE_SdkCells.kind k) =
 (NNE_SdkState.state accounts money (next s a k),sdkReply a k (reply s a k)) := by
 have hf := (NNE_SdkState.fresh_token s fresh a.cell).1
 cases k with
 | shared =>
  by_cases h : sharedOk (s.cells a.cell) = true
  · have hp : (s.cells a.cell).writer = none ∧ (s.cells a.cell).readers.length < 9223372036854775807 := by
     simpa [sharedOk] using h
    simp [NLF_SdkModel.wrap,NLF_RefCell.shared,NNE_SdkCells.kind,NNE_SdkState.state,
      NNE_SdkState.cell,next,reply,allowed,h,hp.1,hp.2,hf,sdkReply,
      RSL.SdkState.put,NLF_SdkModel.put]
    funext j
    by_cases hj : j = a.cell
    · subst j; simp_all [NNE_SdkState.cell]
    · simp_all [NNE_SdkState.cell,hj]
  · have hp : ¬ ((s.cells a.cell).writer = none ∧ (s.cells a.cell).readers.length < 9223372036854775807) := by
     simpa [sharedOk] using h
    simp [NLF_SdkModel.wrap,NLF_RefCell.shared,NNE_SdkCells.kind,NNE_SdkState.state,
      NNE_SdkState.cell,next,reply,allowed,h,hp,hf,sdkReply]
    rfl
 | exclusive =>
  by_cases h : exclusiveOk (s.cells a.cell) = true
  · have hp : (s.cells a.cell).writer = none ∧ (s.cells a.cell).readers = [] := by
     simpa [exclusiveOk] using h
    simp [NLF_SdkModel.wrap,NLF_RefCell.exclusive,NNE_SdkCells.kind,NNE_SdkState.state,
      NNE_SdkState.cell,next,reply,allowed,h,hp.1,hp.2,sdkReply,
      RSL.SdkState.put,NLF_SdkModel.put]
    funext j
    by_cases hj : j = a.cell
    · subst j; simp_all [NNE_SdkState.cell]
    · simp_all [NNE_SdkState.cell,hj]
  · have hp : ¬ ((s.cells a.cell).writer = none ∧ (s.cells a.cell).readers = []) := by
     simpa [exclusiveOk] using h
    simp [NLF_SdkModel.wrap,NLF_RefCell.exclusive,NNE_SdkCells.kind,NNE_SdkState.state,
      NNE_SdkState.cell,next,reply,allowed,h,hp,sdkReply]
    rfl

#print axioms relation
#print axioms sdk_wrap
end NNE_SdkAcquire
