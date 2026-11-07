import NMX_DistinctSuccess
import NMX_CanonicalDistinct
import NMX_ObserveResult
set_option autoImplicit false
noncomputable section
namespace NMX_DistinctCarrier
open Aeneas Aeneas.Std Result AdapterRw NMX_Carrier NMX_ObserveResult
attribute [local instance] Classical.propDecidable

theorem key_nodup (keys : List solana_pubkey.Pubkey) :
 (keys.map key).Nodup ↔ keys.Nodup := by
 simp only [List.nodup_iff_pairwise_ne,List.pairwise_map,NMX_KeyCarrier.key_equal]

theorem criterion (p m c l r e v : r1_pool_adapter.owned.OwnedAccount) :
 RSL.distinctKeys [account p,account m,account c,account l,account r,account e,account v] = true ↔
 [p.key,m.key,c.key,l.key,r.key,e.key,v.key].Nodup := by
 rw [NMX_CanonicalDistinct.keys]
 exact key_nodup [p.key,m.key,c.key,l.key,r.key,e.key,v.key]

theorem seven (ops : Ops) (p m c l r e v : r1_pool_adapter.owned.OwnedAccount) :
 observe (fun u : Unit => u)
  (r1_pool_adapter.owned.require_distinct_accounts (NMX_LeafInstall.install ops)
   (Array.make 7#usize [p,m,c,l,r,e,v])) =
 ⟨.ret (RSL.requireDistinct [account p,account m,account c,account l,account r,account e,account v]),[]⟩ := by
 change observe (fun u : Unit => u)
  (r1_pool_adapter.owned.require_distinct_accounts
   (NGL_ReadonlyModel.install (NMX_LeafInstall.install ops))
   (Array.make 7#usize [p,m,c,l,r,e,v])) = _
 rw [NHJ_DistinctPacket.seven]
 rcases NMX_DistinctValues.reference_values (Array.make 7#usize [p,m,c,l,r,e,v]) with good | bad
 · have unique := (NMX_DistinctSuccess.seven p m c l r e v).mp good
   have admitted := (criterion p m c l r e v).mpr unique
   rw [good]
   simp only [RSL.requireDistinct,admitted,↓reduceIte,observe,NMX_Carrier.reply]
 · have rejected : ¬ RSL.distinctKeys [account p,account m,account c,account l,account r,account e,account v] = true := by
    intro admitted
    have success := (NMX_DistinctSuccess.seven p m c l r e v).mpr ((criterion p m c l r e v).mp admitted)
    rw [bad] at success
    cases success
   rw [bad]
   simp only [RSL.requireDistinct,rejected,↓reduceIte,observe,NMX_Carrier.reply,NMX_Carrier.error]
#print axioms key_nodup
#print axioms criterion
#print axioms seven
end NMX_DistinctCarrier
end
