import NMV_RslFold
import TCK_WeakRoot0
set_option autoImplicit false
namespace NMV_G2
open RSL NMV_RslLaws NMV_RslSnapshots

/-- Every RETURN of the full 240 reference preserves all account payloads,
including cells absent from the account slice and aliased descriptor cells.
No post-state is asserted on an abort or divergence. -/
theorem reference_frame (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (a : TX2_240.Args) (s t : SdkState) (env : Env)
 (reply : Except ProgramError Unit) (events : List Event)
 (h : TX2_240.Ref L D V a s env ⟨.ret (reply,t),events⟩) : PayloadFrame s t := by
 unfold TX2_240.Ref at h
 split at h
 next bad =>
   simp only [Spec.pure,Obs.mk.injEq,Exit.ret.injEq,Prod.mk.injEq] at h
   rcases h with ⟨⟨_,rfl⟩,_⟩
   exact frame_refl _
 next good =>
   obtain ⟨_,_,_,_,h,_⟩ := bind_return _ _ _ _ _ h
   obtain ⟨⟨xs,s1⟩,es,_,hs,h,_⟩ := bind_return _ _ _ _ _ h
   have hf := (snapAll_facts _ _ _ _ _ env es hs).1
   obtain ⟨_,_,_,_,h,_⟩ := bind_return _ _ _ _ _ h
   obtain ⟨_,_,_,_,h,_⟩ := bind_return _ _ _ _ _ h
   obtain ⟨_,_,_,_,h,_⟩ := bind_return _ _ _ _ _ h
   simp only [Spec.pure,Obs.mk.injEq,Exit.ret.injEq,Prod.mk.injEq] at h
   rcases h with ⟨⟨_,rfl⟩,_⟩
   exact hf

/-- G2 at the weak 240 instance: unconditional on entry inputs, and for
EVERY invocation, hence also every non-selected ASQ8 invocation. The root
parameter is an intermediate packet requirement, not an actual native root. -/
theorem weak_frame (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (w : Bytes → Bytes → Bytes → Spec (Except V.VErr Unit))
 (impl : TX2_240.Args → SdkState → Env → Obs (Except ProgramError Unit × SdkState))
 (root : TX2_240.RowSpec_240 L D (TCK.weaken V w) impl)
 (a : TX2_240.Args) (s t : SdkState) (env : Env)
 (reply : Except ProgramError Unit) (events : List Event)
 (returned : impl a s env=⟨.ret (reply,t),events⟩) : PayloadFrame s t := by
 have h := root a s env (TCK.domain240_weaken V w a s)
 rw [returned] at h
 exact reference_frame L D (TCK.weaken V w) a s t env reply events h

/-- Explicit physical-adapter projection. No account may change bytes on
any weak-instance return, whether selected, rejected or successful. -/
theorem weak_payload (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (w : Bytes → Bytes → Bytes → Spec (Except V.VErr Unit))
 (impl : TX2_240.Args → SdkState → Env → Obs (Except ProgramError Unit × SdkState))
 (root : TX2_240.RowSpec_240 L D (TCK.weaken V w) impl)
 (a : TX2_240.Args) (s t : SdkState) (env : Env)
 (reply : Except ProgramError Unit) (events : List Event)
 (returned : impl a s env=⟨.ret (reply,t),events⟩) (account : AccountInfo) :
 payload account t=payload account s :=
 weak_frame L D V w impl root a s t env reply events returned account.cell

#print axioms reference_frame
#print axioms weak_frame
#print axioms weak_payload
end NMV_G2
