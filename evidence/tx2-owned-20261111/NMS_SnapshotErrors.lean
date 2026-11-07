import NMS_CloneReference
set_option autoImplicit false
namespace NMS_SnapshotErrors
open RSL NMS_RSLSuccess NMS_CloneReference

theorem acquire_error (a : AccountInfo) (kind : Kind) (s : SdkState)
 (env : Env) (error : ProgramError) (post : SdkState) (events : List Event)
 (run : acquire a kind s env ⟨.ret (.error error,post),events⟩) :
 error = .accountBorrowFailed := by
 cases kind <;> (unfold acquire at run; dsimp only at run)
 all_goals
  split at run
  · obtain ⟨_,_,_,_,last,_⟩ := bind_return _ _ _ _ _ run
    have impossible := congrArg Prod.fst (pure_return _ _ _ _ last)
    cases impossible
  · obtain ⟨_,_,_,_,last,_⟩ := bind_return _ _ _ _ _ run
    exact Except.error.inj (congrArg Prod.fst (pure_return _ _ _ _ last))

theorem snapshot (a : AccountInfo) (length1 length2 : Nat) (s : SdkState)
 (env : Env) (account : OwnedAccount) (post : SdkState) (events : List Event)
 (run : RSL.snapshot a length1 length2 s env ⟨.ret (account,post),events⟩) :
 SnapshotErrors account := by
 unfold RSL.snapshot at run
 obtain ⟨⟨reply,s1⟩,_,_,first,last,_⟩ := bind_return _ _ _ _ _ run
 cases reply with
 | error error =>
   have err := acquire_error a .shared s env error s1 _ first
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
   dsimp only at stored
   split at stored
   · cases stored
   · exact Or.inr (Except.error.inj stored.symm)

#print axioms acquire_error
#print axioms snapshot
end NMS_SnapshotErrors
