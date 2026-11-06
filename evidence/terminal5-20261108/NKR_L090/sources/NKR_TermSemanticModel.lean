import NKR_TermSemanticSource
import NIH_AtPoint
import RPv_FJk_SemanticWideOnRun
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_TermSemanticModel
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical decoded)
open NKI_InitialPrefix (Public Openings)
open FIz_ConcretePack (embed)

theorem bounds (pub : Public) (hd : NKR_DigestChildren.Domain pub)
 (asset : pub.asset_id.val<2147483647)
 (amount : (core.option.Option.unwrap_or pub.withdrawal_amount 0#u32).val<2147483647) :
 FJa_PublicBounds.Bounds pub := by
 have same : core.option.Option.unwrap_or pub.withdrawal_amount 0#u32=pub.withdrawal_amount.getD 0#u32 := by
  cases pub.withdrawal_amount <;> rfl
 have amount' : (pub.withdrawal_amount.getD 0#u32).val<FJa_PublicBounds.P := by
  rw [←same]
  exact amount
 exact ⟨hd.anchor,hd.nullifier,hd.change,hd.recipient,hd.frontier,hd.nextRoot,hd.nextFrontier,asset,amount'⟩

/-- Complete emitted261 model equality at the actual caller-created boxed
selector. Its native optimized association remains a separate obligation.
No caller-success, selected output or boxed-call equation is a hypothesis. -/
theorem source (pub : Public) (o : Openings) (point : Array NQ 10#usize)
 (hd : NKR_DigestChildren.Domain pub)
 (hz : canonical o.z) (hs : canonical o.succ_z) (hx : canonical o.xor12_z)
 (hp : canonical point) (asset : pub.asset_id.val<2147483647)
 (amount : (core.option.Option.unwrap_or pub.withdrawal_amount 0#u32).val<2147483647) :
 ∃ s, pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point=ok s ∧
 ∃ p : NKR_TermSemanticSource.Packet pub o s,
 pool_v1.pair_forest_semantic_terminal.semantic_packed pub o s=ok p.out ∧
 (fun j=>embed (decoded p.out j))=fun j=>R0P.pack4 ConcretePackBasis.basis
   (fun i=>R0P.SemSource.scalarLaneAt (SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic pub))
     (ValueFamilyFieldTransport.mapOpenings embed (FIw_PublicModel.openings o))
     (fun k=>embed (FIw_PublicModel.selector s k)) (4*j.val+i.val)) := by
 obtain ⟨s,sc,ch,cl,_⟩:=NIH_AtPoint.boxed point hp
 obtain ⟨p,call⟩:=NKR_TermSemanticSource.source pub o s hd hz hs hx ch cl asset amount
 have value:=FJk_SemanticWideOnRun.value pub o s point p.out hz hs hx hp (bounds pub hd asset amount) sc call
 exact ⟨s,sc,p,call,value.2⟩
#print axioms bounds
#print source
#print axioms source
end AspisR1.NKR_TermSemanticModel
end
