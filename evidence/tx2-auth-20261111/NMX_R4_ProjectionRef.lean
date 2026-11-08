import NMX_R4_RegistryProjection
import NMX_R4_BoxProjection
import NMX_R2_SevenList
import NMX_R2_CountReference
set_option autoImplicit false
noncomputable section
namespace NMX_R4_ProjectionRef
open RSL RSL.TX2_233
open NMX_R4_AccountProjection (account)

def args (a : Args) : Args := {a with accounts := a.accounts.map account}

theorem registry (D : DeployedIds) (v pool : B32) (m : OwnedAccount) (master : Master)
 (r e : OwnedAccount) (slot : UInt64) :
 Spec.call TX2_234.Domain (TX2_234.Ref LIBB_PoolLib.library D)
   ⟨v,pool,account m,master,account r,account e,slot⟩ =
 Spec.call TX2_234.Domain (TX2_234.Ref LIBB_PoolLib.library D)
   ⟨v,pool,m,master,r,e,slot⟩ := by
 change Spec.call TX2_234.Domain (TX2_234.Ref LIBB_PoolLib.library D)
   (NMX_R4_RegistryProjection.args ⟨v,pool,m,master,r,e,slot⟩) = _
 funext env obs
 change (True ∧ TX2_234.Ref LIBB_PoolLib.library D
   (NMX_R4_RegistryProjection.args ⟨v,pool,m,master,r,e,slot⟩) env obs) = _
 rw [NMX_R4_RegistryProjection.reference]
 rfl

theorem body (D : DeployedIds) (a : Args) (p m c l r e v : OwnedAccount) :
 TX2_233.body LIBB_PoolLib.library D (args a)
   (account p) (account m) (account c) (account l) (account r) (account e) (account v) =
 TX2_233.body LIBB_PoolLib.library D a p m c l r e v := by
 unfold TX2_233.body
 simp only [NMX_R4_AccountProjection.buffer,NMX_R4_AccountProjection.checkpoint,
  NMX_R4_AccountProjection.readonly]
 have distinct := NMX_R4_AccountProjection.distinct [p,m,c,l,r,e,v]
 simp only [List.map_cons,List.map_nil] at distinct
 rw [distinct]
 simp only [NMX_R4_BoxProjection.master,NMX_R4_BoxProjection.checkpoint,
  NMX_R4_ReadDecode.lane,registry,NMX_R4_BoxProjection.key]
 rfl

theorem reference (D : DeployedIds) (a : Args) :
 Ref LIBB_PoolLib.library D (args a) = Ref LIBB_PoolLib.library D a := by
 by_cases count : a.accounts.length = 7
 · obtain ⟨p,m,c,l,r,e,v,shape⟩ := NMX_R2_SevenList.shape a.accounts count
   have left : Ref LIBB_PoolLib.library D (args a) =
      TX2_233.body LIBB_PoolLib.library D (args a)
        (account p) (account m) (account c) (account l) (account r) (account e) (account v) := by
     simp only [Ref,args,shape,List.map_cons,List.map_nil]
   rw [left,body]
   simp only [Ref,shape]
 · rw [NMX_R2_CountReference.other _ _ a count,
       NMX_R2_CountReference.other _ _ (args a) (by simpa only [args,List.length_map] using count)]
   simp only [args,List.length_map]
#print axioms reference

#print axioms registry
#print axioms body
end NMX_R4_ProjectionRef
end
