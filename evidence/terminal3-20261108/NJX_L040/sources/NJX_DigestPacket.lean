import NJX_DigestPrefix
import NJX_DigestGroups
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_DigestPacket
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open FIv_PreparedNew (NP)
open NJX_DigestResiduals (Digest Residuals)
structure Packet (high : NQ) (o : Residuals) (d : Digest) where
 prepared : NP
 residual : Residuals
 packed : Fin 2 → NQ
 out : Fin 2 → NQ
 constructor : FIq_Native.field.PreparedQm31Multiplier.new high=ok prepared
 domain : NJB_PreparedLaws.Domain prepared high
 cells : ∀ i,NJX_DigestResiduals.Cell o d i (residual i)
 residual_canonical : ∀ i,Canon (residual i)
 residual_value : ∀ i,decode (residual i)=decode (o i)-((d i).val : K)
 prefix : NJB_Traverse.run (NJX_DigestResiduals.reference o d) (List.finRange 8)=ok ⟨List.ofFn residual,by simp⟩
 packs : ∀ g,NJB_PackLaw.reference (NJX_DigestGroups.group residual g)=ok (packed g)
 products : ∀ g,FIq_Native.field.PreparedQm31Multiplier.mul prepared (packed g)=ok (out g)
 out_canonical : ∀ g,Canon (out g)
 out_value : ∀ g,decode (out g)=decode high*NJB_PackLinearity.pack (fun j=>decode (o (NJX_DigestGroups.index g j))-((d (NJX_DigestGroups.index g j)).val : K))

def reference (high : NQ) (o : Residuals) (d : Digest) : Result (Fin 2 → NQ) := do
 let p ← FIq_Native.field.PreparedQm31Multiplier.new high
 let rs ← NJB_Traverse.run (NJX_DigestResiduals.reference o d) (List.finRange 8)
 let r : Residuals := fun i=>rs.val[i.val]'(by rw [rs.property,List.length_finRange];exact i.isLt)
 let a ← NJX_DigestGroups.reference p r 0
 let b ← NJX_DigestGroups.reference p r 1
 ok ![a,b]
/-- Full21-call global-order arithmetic packet; EVERY stub paired at SAME
operands, full9word constructor cache, all8residuals BEFORE both products. -/
theorem source (high : NQ) (o : Residuals) (d : Digest) (hh : Canon high)
 (ho : ∀ i,Canon (o i)) (hd : ∀ i,(d i).val<2147483647) :
 ∃ p : Packet high o d,reference high o d=ok p.out := by
 obtain ⟨cache,cc,hcache⟩ := NJB_PreparedLaws.new_result high hh
 obtain ⟨r,cr,hr,vr,pr⟩ := NJX_DigestPrefix.source o d ho hd
 choose packed out cp hp co call hout vout using (fun g : Fin 2=>NJX_DigestGroups.source cache high r g hh hr hcache)
 have vals : ∀ g,decode (out g)=decode high*NJB_PackLinearity.pack (fun j=>decode (o (NJX_DigestGroups.index g j))-((d (NJX_DigestGroups.index g j)).val : K)) := by
  intro g
  rw [vout]
  congr 2
  funext j
  exact vr _
 let p : Packet high o d := ⟨cache,r,packed,out,cc,hcache,cr,hr,vr,pr,cp,co,hout,vals⟩
 refine ⟨p,?_⟩
 have a := call 0
 have b := call 1
 have same : (![out 0,out 1] : Fin 2 → NQ)=out := by funext i;fin_cases i <;> rfl
 simp only [reference,cc,pr,bind_tc_ok,List.getElem_ofFn]
 change (do let a←NJX_DigestGroups.reference cache r 0;let b←NJX_DigestGroups.reference cache r 1;ok ![a,b])=ok out
 rw [a,bind_tc_ok,b,bind_tc_ok,same]
#print source
#print axioms source
end AspisR1.NJX_DigestPacket
end
