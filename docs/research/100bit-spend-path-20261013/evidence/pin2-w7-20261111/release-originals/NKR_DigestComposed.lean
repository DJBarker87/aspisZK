import NKR_DigestInvocation
import NKR_DigestWrapper
import NKR_DigestWrapperView
import NKR_DigestPrefixStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_DigestComposed
open Aeneas Aeneas.Std Result
open FIv_NativeValue (Canon)
open NKI_InitialPrefix (Public Openings Selectors)
open NKR_DigestCuts (zero)
/-- Full251/250 packet: NEW prefix3event steps composed four times, the
NEW append1/levels-add4/root3/carry4 primitive cuts chained at their SAME full
poststates, NEW projected-wrapper NativeCut and its proved full-carrier
summary, and literal packed whole-old cohort equality. Old whole-prefix/
whole-middle summaries are NOT premises, returned certificates or credit.
All child clauses and arithmetic laws are internally discharged. Canonical
actual root inputs alone remain. Native matched controls and next-ledger
adoption are still required; no K020/K022/K034 timeout confers any credit. -/
theorem source (p : Public) (o : Openings) (s : Selectors)
 (hp : NKR_DigestChildren.Domain p) (ho : FIw_ArrayValue.canonical o.z)
 (hh : FIw_ArrayValue.canonical s.high) (hl : FIw_ArrayValue.canonical s.low) :
 ∃ c sums out old v m,
 NKR_DigestChildren.Clauses p o s c ∧ NKR_DigestChildren.Canonical c ∧
 NKR_DigestInvocation.PrefixArithmetic c v ∧
 NKR_DigestPrefixStep.Trace p o s c (List.finRange 4) ![zero,zero,zero] ![zero,v 3,zero] ∧
 NKR_DigestInvocation.MiddleArithmetic c ![zero,v 3,zero] m ∧
 NKR_DigestCuts.MiddleNative p o s c ![zero,v 3,zero] m ∧
 NKR_DigestCuts.afterCarry m=sums ∧
 NKR_DigestWrapperView.NativeCut p o s p o s out out 1 ∧
 NKR_DigestCuts.WrapperCut p o s p o s out out 1 ∧
 NKR_DigestPrefix.run p o s=ok (c,sums) ∧ NKR_DigestPrefix.Frame c sums ∧
 NKR_DigestComplete.reference p o s=ok out ∧ NKR_DigestWrapper.reference p o s=ok out ∧
 NKR_DigestWrapper.cohort p o s=ok out ∧ (∀ j,Canon (out j)) ∧
 FIq_Native.pool_v1.pair_forest_semantic_terminal.public_digest_lanes p o s=ok old ∧ FIw_ArrayValue.canonical old := by
 obtain ⟨c,sums,out,old,hc,hcan,pc,frame,oc,wc,cc,hout,oldc,hold⟩ := NKR_DigestWrapper.source p o s hp ho hh hl
 obtain ⟨v,m,vc,mc,native,sc,_⟩ := NKR_DigestInvocation.source p o s c hc hcan
 have same : NKR_DigestCuts.afterCarry m=sums :=
  congrArg Prod.snd (Result.ok.inj (sc.symm.trans pc))
 have wrapperNative:=NKR_DigestWrapperView.native_cut p o s out
 have wrapperSummary:=NKR_DigestWrapperView.native_summary p p o o s s out out 1 wrapperNative
 exact ⟨c,sums,out,old,v,m,hc,hcan,vc,NKR_DigestPrefixStep.four p o s c v vc,
  mc,native,same,wrapperNative,wrapperSummary,pc,frame,oc,wc,cc,hout,oldc,hold⟩
#print source
#print axioms source
end AspisR1.NKR_DigestComposed
end
