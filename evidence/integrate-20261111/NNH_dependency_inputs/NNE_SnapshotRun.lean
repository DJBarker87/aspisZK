import NNE_Snapshot
import NNE_SdkRelease
import NMV_RslLaws
set_option autoImplicit false
noncomputable section
namespace NNE_SnapshotRun
open RSL

theorem put_same (s : SdkState) (i : Nat) : s.put i (s.cells i) = s := by
 cases s with
 | mk cells next =>
  simp only [SdkState.put,SdkState.mk.injEq,true_and,and_true]
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [h]

theorem put_twice (s : SdkState) (i : Nat) (c d : Cell) :
 (s.put i c).put i d = s.put i d := by
 cases s with
 | mk cells next =>
  simp only [SdkState.put,SdkState.mk.injEq,true_and,and_true]
  funext j
  by_cases h : j = i <;> simp [h]

/-- Successful entry snapshot has its complete bytes and metadata; the only
nonreturning alternative is failure of the named admitted-length allocation. -/
theorem returned (e : AspisR1.S2W_D189Entry.Entry) (n i l1 l2 : Nat)
 (env : Env) (x : OwnedAccount) (post : SdkState) (es : List Event)
 (h : snapshot (NNE_Entry.account e i) l1 l2 (NNE_Entry.state e n) env ⟨.ret (x,post),es⟩) :
 x = NNE_Snapshot.view (NNE_Entry.account e i) (NNE_Entry.state e n) l1 l2 ∧
 post = NNE_Entry.state e (n+1) := by
 unfold snapshot at h
 obtain ⟨⟨r,s1⟩,e1,e2,ha,hk,_⟩ := NMV_RslLaws.bind_return _ _ _ _ _ h
 have eq := (NNE_SdkAcquire.relation _ _ .shared env _).mp ha
 simp only [NNE_SdkAcquire.reply,NNE_SdkAcquire.next,NNE_SdkAcquire.allowed,
  sharedOk,NNE_Entry.state,Option.isNone_none,Bool.true_and,List.length_nil,
  Nat.zero_lt_succ,decide_true,if_true,Obs.mk.injEq,Exit.ret.injEq,Prod.mk.injEq] at eq
 rcases eq with ⟨⟨rfl,rfl⟩,_⟩
 dsimp only at hk
 obtain ⟨_,_,_,_,hk,_⟩ := NMV_RslLaws.bind_return _ _ _ _ _ hk
 obtain ⟨s2,_,_,hr,hp,_⟩ := NMV_RslLaws.bind_return _ _ _ _ _ hk
 have hr' := (NNE_SdkRelease.relation _ _ _ .shared env _).mp hr
 simp only [Obs.mk.injEq,Exit.ret.injEq] at hr'
 rcases hr' with ⟨rfl,_⟩
 simp only [Spec.pure,Obs.mk.injEq,Exit.ret.injEq,Prod.mk.injEq] at hp
 rcases hp with ⟨⟨rfl,rfl⟩,_⟩
 constructor
 · simp [NNE_Snapshot.view,payload,NNE_Entry.state,NNE_SdkRelease.next,SdkState.put]
 · simp only [NNE_SdkRelease.next,NNE_Entry.state,SdkState.put]
   congr 1
   funext j
   by_cases hj : j = (NNE_Entry.account e i).cell
   · subst j; simp
   · simp [hj]
#print axioms put_same
#print axioms put_twice
#print axioms returned
end NNE_SnapshotRun
end
