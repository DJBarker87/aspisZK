import NMV_RslSnapshots
set_option autoImplicit false
namespace NMV_SdkFrame
open RSL NMV_RslLaws

def sharedState (a : AccountInfo) (s : SdkState) : SdkState :=
 { (s.put a.cell {s.cells a.cell with readers:=s.next::(s.cells a.cell).readers}) with next:=s.next+1 }

theorem shared_ok (a : AccountInfo) (s t : SdkState) (token : Nat)
 (env : Env) (es : List Event)
 (h : acquire a .shared s env ⟨.ret (.ok token,t),es⟩) :
 token=s.next ∧ t=sharedState a s := by
 unfold acquire at h
 simp only at h
 split at h
 all_goals
  obtain ⟨_,hp,_⟩ := emit_return _ _ _ _ _ h
  simp only [Spec.pure,Obs.mk.injEq,Exit.ret.injEq,Prod.mk.injEq] at hp
 · exact ⟨Except.ok.inj hp.1.1,hp.1.2⟩
 · cases hp.1.1

theorem shared_error (a : AccountInfo) (s t : SdkState) (e : ProgramError)
 (env : Env) (es : List Event)
 (h : acquire a .shared s env ⟨.ret (.error e,t),es⟩) :
 t={s with next:=s.next+1} := by
 unfold acquire at h
 simp only at h
 split at h
 all_goals
  obtain ⟨_,hp,_⟩ := emit_return _ _ _ _ _ h
  simp only [Spec.pure,Obs.mk.injEq,Exit.ret.injEq,Prod.mk.injEq] at hp
 · cases hp.1.1
 · exact hp.1.2

theorem snapshot_sdk (a : AccountInfo) (l1 l2 : Nat) (s t : SdkState)
 (x : OwnedAccount) (env : Env) (es : List Event)
 (h : snapshot a l1 l2 s env ⟨.ret (x,t),es⟩) :
 t.cells=s.cells ∧ t.next=s.next+1 := by
 obtain ⟨⟨reply,s1⟩,e1,_,ha,hk,_⟩ := bind_return _ _ _ _ _ h
 cases reply with
 | error e =>
   have eq := shared_error a s s1 e env e1 ha
   simp only [Spec.pure,Obs.mk.injEq,Exit.ret.injEq,Prod.mk.injEq] at hk
   rcases hk with ⟨⟨_,rfl⟩,_⟩
   rw [eq]
   exact ⟨rfl,rfl⟩
 | ok token =>
   obtain ⟨ht,hs⟩ := shared_ok a s s1 token env e1 ha
   obtain ⟨_,_,_,_,hk,_⟩ := bind_return _ _ _ _ _ hk
   obtain ⟨s2,_,_,hr,hp,_⟩ := bind_return _ _ _ _ _ hk
   simp only [Spec.pure,Obs.mk.injEq,Exit.ret.injEq,Prod.mk.injEq] at hp
   rcases hp with ⟨⟨_,rfl⟩,_⟩
   unfold release at hr
   obtain ⟨_,hr,_⟩ := emit_return _ _ _ _ _ hr
   simp only [Spec.pure,Obs.mk.injEq,Exit.ret.injEq] at hr
   rcases hr with ⟨rfl,_⟩
   subst token
   subst s1
   constructor
   · funext i
     by_cases hi : i=a.cell <;> simp [sharedState,SdkState.put,hi]
   · rfl

/-- ALL SDK cells, including their borrow tokens, are restored on every
returned snapshot sequence. Only the fresh-token counter advances. -/
theorem snapshots_sdk (as : List AccountInfo) (ls : List (Nat × Nat))
 (s t : SdkState) (xs : List OwnedAccount) (env : Env) (es : List Event)
 (h : TX2_240.snapAll as ls s env ⟨.ret (xs,t),es⟩) :
 t.cells=s.cells ∧ t.next=s.next+min as.length ls.length := by
 induction as generalizing ls s t xs es with
 | nil =>
   simp only [TX2_240.snapAll,Spec.pure,Obs.mk.injEq,Exit.ret.injEq,Prod.mk.injEq] at h
   rcases h with ⟨⟨_,rfl⟩,_⟩
   simp
 | cons a as ih =>
   cases ls with
   | nil =>
     simp only [TX2_240.snapAll,Spec.pure,Obs.mk.injEq,Exit.ret.injEq,Prod.mk.injEq] at h
     rcases h with ⟨⟨_,rfl⟩,_⟩
     simp
   | cons l ls =>
     obtain ⟨⟨x,s1⟩,e1,_,ha,hk,_⟩ := bind_return _ _ _ _ _ h
     have hf := snapshot_sdk a l.1 l.2 s s1 x env e1 ha
     obtain ⟨⟨ys,s2⟩,e2,_,hb,hp,_⟩ := bind_return _ _ _ _ _ hk
     have hg := ih ls s1 s2 ys e2 hb
     simp only [Spec.pure,Obs.mk.injEq,Exit.ret.injEq,Prod.mk.injEq] at hp
     rcases hp with ⟨⟨_,rfl⟩,_⟩
     constructor
     · exact hg.1.trans hf.1
     · rw [hg.2,hf.2]
       simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

#print axioms shared_ok
#print axioms shared_error
#print axioms snapshot_sdk
#print axioms snapshots_sdk
end NMV_SdkFrame
