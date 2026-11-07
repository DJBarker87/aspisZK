import NNE_SnapshotRun
set_option autoImplicit false
noncomputable section
namespace NNE_SnapshotSequence
open RSL AspisR1.S2W_D189Entry

def views (e : Entry) (indices : List Nat) (lenses : List (Nat × Nat)) : List OwnedAccount :=
 List.zipWith (fun i l => NNE_Snapshot.view (NNE_Entry.account e i) (NNE_Entry.state e 0) l.1 l.2)
  indices lenses

theorem returned (e : Entry) (indices : List Nat) (lenses : List (Nat × Nat))
 (n : Nat) (env : Env) (xs : List OwnedAccount) (post : SdkState) (es : List Event)
 (h : TX2_240.snapAll (indices.map (NNE_Entry.account e)) lenses (NNE_Entry.state e n)
  env ⟨.ret (xs,post),es⟩) :
 xs = views e indices lenses ∧
 post = NNE_Entry.state e (n + min indices.length lenses.length) := by
 induction indices generalizing lenses n xs post es with
 | nil =>
  simp only [List.map_nil,TX2_240.snapAll,Spec.pure,Obs.mk.injEq,Exit.ret.injEq,Prod.mk.injEq] at h
  rcases h with ⟨⟨rfl,rfl⟩,_⟩
  exact ⟨rfl,rfl⟩
 | cons i indices ih =>
  cases lenses with
  | nil =>
   simp only [List.map_cons,TX2_240.snapAll,Spec.pure,Obs.mk.injEq,Exit.ret.injEq,Prod.mk.injEq] at h
   rcases h with ⟨⟨rfl,rfl⟩,_⟩
   exact ⟨rfl,by simp⟩
  | cons l lenses =>
   obtain ⟨⟨x,s1⟩,e1,_,hs,hk,_⟩ := NMV_RslLaws.bind_return _ _ _ _ _ h
   obtain ⟨hx,ht⟩ := NNE_SnapshotRun.returned e n i l.1 l.2 env x s1 e1 hs
   subst x; subst s1
   obtain ⟨⟨ys,s2⟩,e2,_,hr,hp,_⟩ := NMV_RslLaws.bind_return _ _ _ _ _ hk
   obtain ⟨hy,hpost⟩ := ih lenses (n+1) ys s2 e2 hr
   simp only [Spec.pure,Obs.mk.injEq,Exit.ret.injEq,Prod.mk.injEq] at hp
   rcases hp with ⟨⟨rfl,rfl⟩,_⟩
   constructor
   · change _ :: ys = _ :: views e indices lenses
     rw [hy]
     rfl
   · rw [hpost]
     congr 1
     simp only [List.length_cons]
     omega

theorem first (err : NNE_Snapshot.PE → ProgramError)
 (invalid : err .InvalidAccountData = .invalidAccountData) (e : Entry) (n : Nat)
 (env : Env) (xs : List OwnedAccount) (post : SdkState) (es : List Event)
 (h : TX2_240.snapAll ((List.range 3).map (NNE_Entry.account e)) TX1_344.snapLens
   (NNE_Entry.state e n) env ⟨.ret (xs,post),es⟩) :
 xs = e.first.val.map (NNE_Snapshot.owned err) ∧ post = NNE_Entry.state e (n+3) := by
 obtain ⟨hv,hp⟩ := returned e (List.range 3) TX1_344.snapLens n env xs post es h
 constructor
 · rw [hv,NNE_Snapshot.first_snapshots err invalid e 0]
   rfl
 · simpa [TX1_344.snapLens,List.length_range] using hp

theorem second (err : NNE_Snapshot.PE → ProgramError)
 (invalid : err .InvalidAccountData = .invalidAccountData) (e : Entry) (n : Nat)
 (env : Env) (xs : List OwnedAccount) (post : SdkState) (es : List Event)
 (h : TX2_240.snapAll ((List.range 7).map (NNE_Entry.account e)) TX2_240.snapLens
   (NNE_Entry.state e n) env ⟨.ret (xs,post),es⟩) :
 xs = (e.second AspisR1.S2W_D189Wrappers.secondSizes).val.map (NNE_Snapshot.owned err) ∧
 post = NNE_Entry.state e (n+7) := by
 obtain ⟨hv,hp⟩ := returned e (List.range 7) TX2_240.snapLens n env xs post es h
 constructor
 · rw [hv,NNE_Snapshot.second_snapshots err invalid e 0]
   rfl
 · simpa [TX2_240.snapLens,List.length_range] using hp
#print axioms returned
#print axioms first
#print axioms second
end NNE_SnapshotSequence
end
