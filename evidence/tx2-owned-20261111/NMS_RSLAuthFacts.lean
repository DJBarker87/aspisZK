import NMS_RSLRefine
set_option autoImplicit false
namespace NMS_RSLAuthFacts
open RSL NMS_RSLRefine

theorem body_checkpoint (L : PoolLib) (D : DeployedIds) (a : TX2_233.Args)
 (p m c l r e v : OwnedAccount) (env : Env) (auth : Authenticated) (events : List Event)
 (run : TX2_233.body L D a p m c l r e v env ⟨.ret (.ok auth),events⟩) :
 verifierCheckpoint v a.verifier_program false = .ok () := by
 unfold TX2_233.body at run
 obtain ⟨_,_,_,_,run,_⟩ := rsbind_return _ _ _ _ _ run
 obtain ⟨u,_,_,checked,_,_⟩ := rsbind_return _ _ _ _ _ run
 cases u
 exact ofExcept_return _ _ _ _ checked

theorem checkpoint (L : PoolLib) (D : DeployedIds) (a : TX2_233.Args)
 (env : Env) (auth : Authenticated) (events : List Event)
 (run : TX2_233.Ref L D a env ⟨.ret (.ok auth),events⟩) :
 a.accounts.length = 7 ∧ ∃ v, a.accounts[6]? = some v ∧
 verifierCheckpoint v a.verifier_program false = .ok () := by
 unfold TX2_233.Ref at run
 split at run
 next p m c l r e v shape =>
   refine ⟨?_,v,?_,body_checkpoint L D a p m c l r e v env auth events run⟩
   · rw [shape]; rfl
   · rw [shape]; rfl
 next shape =>
   have h := congrArg Obs.exit run
   cases h

#print axioms body_checkpoint
#print axioms checkpoint
end NMS_RSLAuthFacts
