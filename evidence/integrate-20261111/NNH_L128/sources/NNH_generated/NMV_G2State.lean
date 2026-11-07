import NMV_G2
import NMV_SdkFrame
set_option autoImplicit false
namespace NMV_G2State
open RSL NMV_RslLaws NMV_SdkFrame

theorem reference_sdk (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (a : TX2_240.Args) (s t : SdkState) (env : Env)
 (reply : Except ProgramError Unit) (events : List Event)
 (h : TX2_240.Ref L D V a s env ⟨.ret (reply,t),events⟩) :
 t.cells=s.cells ∧ t.next=s.next+(if TX2_240.badRoute a then 0 else 7) := by
 unfold TX2_240.Ref at h
 split at h
 next bad =>
   simp only [Spec.pure,Obs.mk.injEq,Exit.ret.injEq,Prod.mk.injEq] at h
   rcases h with ⟨⟨_,rfl⟩,_⟩
   simp [bad]
 next good =>
   have h7 : a.accounts.length=7 := by
     by_cases hh : a.accounts.length=7
     · exact hh
     · simp [TX2_240.badRoute,hh] at good
   obtain ⟨_,_,_,_,h,_⟩ := bind_return _ _ _ _ _ h
   obtain ⟨⟨xs,s1⟩,es,_,hs,h,_⟩ := bind_return _ _ _ _ _ h
   have hf := snapshots_sdk a.accounts TX2_240.snapLens s s1 xs env es hs
   obtain ⟨_,_,_,_,h,_⟩ := bind_return _ _ _ _ _ h
   obtain ⟨_,_,_,_,h,_⟩ := bind_return _ _ _ _ _ h
   obtain ⟨_,_,_,_,h,_⟩ := bind_return _ _ _ _ _ h
   simp only [Spec.pure,Obs.mk.injEq,Exit.ret.injEq,Prod.mk.injEq] at h
   rcases h with ⟨⟨_,rfl⟩,_⟩
   simpa only [good,Bool.false_eq_true,if_false,h7,TX2_240.snapLens,List.length_cons,List.length_nil,Nat.min_self] using hf

/-- G2 with the entire SDK state exposed: all cells (payload AND readers AND
writer) are unchanged; exactly seven token attempts occur on an admitted
route. No Root0 assumption, no alias restriction, and no post-abort world. -/
theorem weak_sdk (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (w : Bytes → Bytes → Bytes → Spec (Except V.VErr Unit))
 (impl : TX2_240.Args → SdkState → Env → Obs (Except ProgramError Unit × SdkState))
 (root : TX2_240.RowSpec_240 L D (TCK.weaken V w) impl)
 (a : TX2_240.Args) (s t : SdkState) (env : Env)
 (reply : Except ProgramError Unit) (events : List Event)
 (returned : impl a s env=⟨.ret (reply,t),events⟩) :
 t.cells=s.cells ∧ t.next=s.next+(if TX2_240.badRoute a then 0 else 7) := by
 have h := root a s env (TCK.domain240_weaken V w a s)
 rw [returned] at h
 exact reference_sdk L D (TCK.weaken V w) a s t env reply events h

#print axioms reference_sdk
#print axioms weak_sdk
end NMV_G2State
