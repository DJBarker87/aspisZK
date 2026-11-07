import NNH_AuthEval
import NNH_MAccountCarrier
set_option autoImplicit false
namespace NNH_AuthSevenShape
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_ModelCarrier

theorem value (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (program pool : solana_pubkey.Pubkey) (xs : Slice r1_pool_adapter.owned.OwnedAccount)
 (lane : U8) (slot : U64) (out : RSL.Authenticated)
 (success : NNH_AuthEval.value L D ⟨key program,accounts xs,key pool,byte lane,NND_Carrier.slot slot⟩ env=.ok out) :
 ∃ p m c l r e v,xs.val=[p,m,c,l,r,e,v] ∧
 NNH_AuthEval.bodyValue L D ⟨key program,accounts xs,key pool,byte lane,NND_Carrier.slot slot⟩
  (account p) (account m) (account c) (account l) (account r) (account e) (account v) env=.ok out := by
 unfold NNH_AuthEval.value accounts at success
 generalize hxs : xs.val=rest at success
 cases rest with
 | nil => cases success
 | cons p rest => cases rest with
   | nil => cases success
   | cons m rest => cases rest with
     | nil => cases success
     | cons c rest => cases rest with
       | nil => cases success
       | cons l rest => cases rest with
         | nil => cases success
         | cons r rest => cases rest with
           | nil => cases success
           | cons e rest => cases rest with
             | nil => cases success
             | cons v rest => cases rest with
               | cons extra rest => cases success
               | nil =>
                refine ⟨p,m,c,l,r,e,v,rfl,?_⟩
                simpa only [accounts,hxs,List.map_cons,List.map_nil] using success
#print axioms value
end NNH_AuthSevenShape
