import NKR_DigestInvocation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_DigestComposed
open Aeneas Aeneas.Std Result
open FIv_NativeValue (Canon)
open NKI_InitialPrefix (Public Openings Selectors)
open NKR_DigestCuts (zero)
/-- Full251/250 packet root: exact native parent typed cuts, SAME source child
clauses, all channels, and literal packed whole-old cohort equality. No cut,
child-success, output, execution or dictionary hypothesis is retained. Native
credit requires the matched Kani certificates for these reviewed(ai)(5)cuts;
NKI/NJX child adoption and this packet await the next authoritative ledger. -/
theorem source (p : Public) (o : Openings) (s : Selectors)
 (hp : NKR_DigestChildren.Domain p) (ho : FIw_ArrayValue.canonical o.z)
 (hh : FIw_ArrayValue.canonical s.high) (hl : FIw_ArrayValue.canonical s.low) :
 ∃ c sums out old v m,
 NKR_DigestChildren.Clauses p o s c ∧ NKR_DigestChildren.Canonical c ∧
 NKR_DigestInvocation.PrefixArithmetic c v ∧
 NKR_DigestInvocation.MiddleArithmetic c ![zero,v 3,zero] m ∧
 NKR_DigestCuts.PrefixCut p o s c v ![zero,v 3,zero] (NKR_DigestCuts.prefixEvents p o s c v) 12 s.high o.succ_z o.xor12_z ∧
 NKR_DigestCuts.MiddleCut p o s c ![zero,v 3,zero] m sums
  (NKR_DigestCuts.middleEvents p o s c ![zero,v 3,zero] m) 12 ∧
 NKR_DigestCuts.WrapperCut p o s p o s out out 1 ∧
 NKR_DigestPrefix.run p o s=ok (c,sums) ∧ NKR_DigestPrefix.Frame c sums ∧
 NKR_DigestComplete.reference p o s=ok out ∧ NKR_DigestWrapper.reference p o s=ok out ∧
 NKR_DigestWrapper.cohort p o s=ok out ∧ (∀ j,Canon (out j)) ∧
 FIq_Native.pool_v1.pair_forest_semantic_terminal.public_digest_lanes p o s=ok old ∧ FIw_ArrayValue.canonical old := by
 obtain ⟨c,sums,out,old,hc,hcan,pc,frame,oc,wc,cc,hout,oldc,hold⟩ := NKR_DigestWrapper.source p o s hp ho hh hl
 obtain ⟨v,m,vc,mc,cutp,cutm,sc,_⟩ := NKR_DigestInvocation.source p o s c hc hcan
 have same : (![m.local0,m.carried,m.local12] : NKR_DigestCuts.Sums)=sums :=
  congrArg Prod.snd (Result.ok.inj (sc.symm.trans pc))
 rw [same] at cutm
 exact ⟨c,sums,out,old,v,m,hc,hcan,vc,mc,cutp,cutm,NKR_DigestCuts.wrapper_cut p o s out,
  pc,frame,oc,wc,cc,hout,oldc,hold⟩
#print source
#print axioms source
end AspisR1.NKR_DigestComposed
end
