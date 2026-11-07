import NMS_SnapshotErrors
import NMS_SafePackets
set_option autoImplicit false
namespace NMS_SnapshotBoth
open RSL NMS_RSLSuccess NMS_SafePackets

theorem length_errors (a : AccountInfo) (length1 length2 : Nat) (s : SdkState)
 (env : Env) (account : OwnedAccount) (post : SdkState) (events : List Event)
 (run : snapshot a length1 length2 s env ⟨.ret (account,post),events⟩) :
 LengthErrors account := by
 unfold snapshot at run
 obtain ⟨⟨reply,s1⟩,_,_,first,last,_⟩ := bind_return _ _ _ _ _ run
 cases reply with
 | error error =>
   have err := NMS_SnapshotErrors.acquire_error a .shared s env error s1 _ first
   have same := congrArg Prod.fst (pure_return _ _ _ _ last)
   dsimp only at same
   rw [same]
   intro e stored
   have eq : e = error := Except.error.inj stored.symm
   exact Or.inl (eq.trans err)
 | ok token =>
   obtain ⟨_,_,_,_,last,_⟩ := bind_return _ _ _ _ _ last
   obtain ⟨s2,_,_,_,last,_⟩ := bind_return _ _ _ _ _ last
   have same := congrArg Prod.fst (pure_return _ _ _ _ last)
   dsimp only at same
   rw [same]
   intro e stored
   cases stored

theorem both (a : AccountInfo) (length1 length2 : Nat) (s : SdkState)
 (env : Env) (account : OwnedAccount) (post : SdkState) (events : List Event)
 (run : snapshot a length1 length2 s env ⟨.ret (account,post),events⟩) :
 NMS_CloneReference.SnapshotErrors account ∧ LengthErrors account :=
 ⟨NMS_SnapshotErrors.snapshot a length1 length2 s env account post events run,
  length_errors a length1 length2 s env account post events run⟩
#print axioms length_errors
#print axioms both
end NMS_SnapshotBoth
