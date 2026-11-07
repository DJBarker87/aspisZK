import NNE_SdkAcquire
import NNE_SdkRelease
set_option autoImplicit false
namespace NNE_SdkParent
open RSL
/-- The parent operation agrees after mapping cell identity and the COMPLETE
reply; old SDK event history is retained as a prefix. -/
theorem acquire (accounts : Nat → NLF_SdkModel.Account) (money : Nat → Nat)
 (s : SdkState) (a : AccountInfo) (index : Nat) (k : Kind)
 (events : List NLF_ParentModel.Event) (identity : (accounts index).data = a.cell)
 (fresh : NNE_SdkState.Fresh s) :
 NLF_ParentModel.acquire (NNE_SdkState.parent accounts money s events) index (NNE_SdkCells.kind k) =
 (NNE_SdkState.parent accounts money (NNE_SdkAcquire.next s a k)
  (events ++ [.acquire index s.next (NNE_SdkCells.kind k)
   (NNE_SdkAcquire.sdkReply a k (NNE_SdkAcquire.reply s a k))]),
  NNE_SdkAcquire.sdkReply a k (NNE_SdkAcquire.reply s a k)) := by
 unfold NLF_ParentModel.acquire NNE_SdkState.parent
 simp only [NNE_SdkState.state,identity]
 change (let r := NLF_SdkModel.wrap (NNE_SdkState.state accounts money s) a.cell s.next (NNE_SdkCells.kind k)
         (NLF_ParentModel.Parent.mk r.1 (s.next+1)
           (events ++ [.acquire index s.next (NNE_SdkCells.kind k) r.2]),r.2)) = _
 rw [NNE_SdkAcquire.sdk_wrap accounts money s a k fresh]
 have hn : (NNE_SdkAcquire.next s a k).next = s.next+1 := by
  unfold NNE_SdkAcquire.next; split <;> rfl
 simp only [hn]
 rfl

/-- An acquired RSL token is exactly the guard the mapped SDK reply owns. -/
theorem guard_identity (a : AccountInfo) (k : Kind) (t : Nat) :
 NNE_SdkAcquire.sdkReply a k (.ok t) = .ok ⟨a.cell,t,NNE_SdkCells.kind k⟩ := rfl
#print axioms acquire
#print axioms guard_identity
end NNE_SdkParent
