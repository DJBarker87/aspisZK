import NMV_RslFold
set_option autoImplicit false
namespace NMV_Stage1Frame
open RSL NMV_RslLaws NMV_RslSnapshots

theorem copy_other (acc : AccountInfo) (ck : Bytes) (s t : SdkState)
 (env : Env) (reply : Except ProgramError Unit) (events : List Event)
 (h : TX1_344.copyStep acc ck s env ⟨.ret (reply,t),events⟩)
 (i : Nat) (other : i≠acc.cell) : (t.cells i).payload=(s.cells i).payload := by
 unfold TX1_344.copyStep at h
 obtain ⟨⟨r,s1⟩,e1,_,ha,hk,_⟩ := bind_return _ _ _ _ _ h
 have hf := acquire_frame acc .exclusive s s1 r env e1 ha
 cases r with
 | error e =>
   simp only [Spec.pure,Obs.mk.injEq,Exit.ret.injEq,Prod.mk.injEq] at hk
   rcases hk with ⟨⟨_,rfl⟩,_⟩
   exact hf i
 | ok token =>
   dsimp only at hk
   split at hk
   · cases congrArg Obs.exit hk
   · obtain ⟨_,_,_,_,hk,_⟩ := bind_return _ _ _ _ _ hk
     obtain ⟨s2,es,_,hr,hp,_⟩ := bind_return _ _ _ _ _ hk
     have hg := release_frame acc token .exclusive _ s2 env es hr
     simp only [Spec.pure,Obs.mk.injEq,Exit.ret.injEq,Prod.mk.injEq] at hp
     rcases hp with ⟨⟨_,rfl⟩,_⟩
     exact (hg i).trans (by simpa [SdkState.put,other] using hf i)

/-- Canonical 344's account-data frame. The write footprint is the cell of
accounts[2], allowing duplicate descriptors to share that same cell. -/
theorem reference_other (V : VLib) (P : PreparedNew V) (C : TX1_345.S1Lib V)
 (a : TX1_344.Args) (s t : SdkState) (env : Env)
 (reply : Except ProgramError Unit) (events : List Event)
 (h : TX1_344.Ref V P C a s env ⟨.ret (reply,t),events⟩)
 (acc : AccountInfo) (at2 : a.accounts[2]?=some acc)
 (i : Nat) (other : i≠acc.cell) : (t.cells i).payload=(s.cells i).payload := by
 unfold TX1_344.Ref at h
 split at h
 · simp only [Spec.pure,Obs.mk.injEq,Exit.ret.injEq,Prod.mk.injEq] at h
   rcases h with ⟨⟨_,rfl⟩,_⟩
   rfl
 · obtain ⟨⟨xs,s1⟩,e1,_,hs,hk,_⟩ := bind_return _ _ _ _ _ h
   have hf := (snapAll_facts _ _ _ _ _ env e1 hs).1
   obtain ⟨r,_,es,_,hk,_⟩ := bind_return _ _ _ _ _ hk
   cases r with
   | error e =>
     simp only [Spec.pure,Obs.mk.injEq,Exit.ret.injEq,Prod.mk.injEq] at hk
     rcases hk with ⟨⟨_,rfl⟩,_⟩
     exact hf i
   | ok ck =>
     rw [at2] at hk
     exact (copy_other acc ck s1 t env reply es hk i other).trans (hf i)

#print axioms copy_other
#print axioms reference_other
end NMV_Stage1Frame
