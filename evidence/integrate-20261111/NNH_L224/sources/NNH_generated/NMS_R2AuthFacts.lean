import NMS_R2Getters
set_option autoImplicit false
namespace NMS_R2AuthFacts
open RSL NMS_R2Refine

theorem body_checkpoint (L : PoolLib) (D : DeployedIds) (a : TX2_233.Args)
 (p m c l r e v : OwnedAccount) (env : Env) (auth : Authenticated) (events : List Event)
 (run : TX2_233.body L D a p m c l r e v env ⟨.ret (.ok auth),events⟩) :
 v.length = .ok CHECKPOINT_BYTES := by
 unfold TX2_233.body at run
 obtain ⟨_,_,_,_,run,_⟩ := rsbind_return _ _ _ _ _ run
 obtain ⟨u,_,_,checked,_,_⟩ := rsbind_return _ _ _ _ _ run
 cases u
 exact NMS_R2Getters.checkpoint_success _ _ _ _ _ checked

theorem checkpoint (L : PoolLib) (D : DeployedIds) (a : TX2_233.Args)
 (env : Env) (auth : Authenticated) (events : List Event)
 (run : TX2_233.Ref L D a env ⟨.ret (.ok auth),events⟩) :
 a.accounts.length = 7 ∧ ∃ v, a.accounts[6]? = some v ∧
 v.length = .ok CHECKPOINT_BYTES := by
 unfold TX2_233.Ref at run
 generalize shape : a.accounts = accounts at run ⊢
 cases accounts with
 | nil => have impossible := congrArg Obs.exit run; cases impossible
 | cons p rest1 =>
   cases rest1 with
   | nil => have impossible := congrArg Obs.exit run; cases impossible
   | cons m rest2 =>
     cases rest2 with
     | nil => have impossible := congrArg Obs.exit run; cases impossible
     | cons c rest3 =>
       cases rest3 with
       | nil => have impossible := congrArg Obs.exit run; cases impossible
       | cons l rest4 =>
         cases rest4 with
         | nil => have impossible := congrArg Obs.exit run; cases impossible
         | cons r rest5 =>
           cases rest5 with
           | nil => have impossible := congrArg Obs.exit run; cases impossible
           | cons e rest6 =>
             cases rest6 with
             | nil => have impossible := congrArg Obs.exit run; cases impossible
             | cons v rest7 =>
               cases rest7 with
               | nil =>
                 exact ⟨rfl,v,rfl,body_checkpoint L D a p m c l r e v env auth events run⟩
               | cons extra remaining => have impossible := congrArg Obs.exit run; cases impossible

#print axioms body_checkpoint
#print axioms checkpoint
end NMS_R2AuthFacts
