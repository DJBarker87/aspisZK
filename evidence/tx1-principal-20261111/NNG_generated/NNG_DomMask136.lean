import NNG_DomRecord25_136
import NNG_SelectedMaskCanonical
import NNG_ProjectMaskDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DomMask136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_Transport
open NNG_TraceAll136 NNG_TypedDomains136 NNG_LIBScalar NNG_LIBArrayDomain NNG_LIBClaimsDomain

theorem mask {W : Type} (fallback : Value) (c : Calls) (env : RSL.Env) (source : NNG_SourceCalls136.Sources c env)
    (s : Parent Unit W) (p : LIB_VCarriers.Prefix) (prefixEq : s.prefixValue=NNG_LIBData.lowerPrefix p)
    (running terminal : Q) (alpha : Alpha) (claims : Claims) (t1 : r1_wire.SemanticTranscript Unit)
    (etaDom : Domain s.challenges.eta) (terminalDom : Domain terminal) (alphaDom : DomainArray alpha) (claimsDom : DomainClaims claims) :
    All Checked (NNG_TreeSuffixes.f_mask c s running terminal (NNG_Array136.cell claims 27#usize (by decide)) alpha t1 claims
      (NNG_FromFnValues136.low claims) (NNG_FromFnValues136.high claims)) := by
  have lowDom := NNG_SelectedMaskCanonical.low claims claimsDom
  have highDom := NNG_SelectedMaskCanonical.high claims claimsDom
  have blindDom := NNG_SelectedMaskCanonical.cell claims claimsDom 27#usize (by decide)
  let low := NNG_FromFnValues136.low claims
  let high := NNG_FromFnValues136.high claims
  let blind := NNG_Array136.cell claims 27#usize (by decide)
  unfold NNG_TreeSuffixes.f_mask
  refine NNG_TraceAll136.bind Checked (NMT_CallTree.invoke "mask" (low,high,blind,alpha) (c.c6 low high blind alpha)) _ ?_ ?_
  · exact NNG_TraceAll136.invoke Checked _ _ _ (NNG_CheckedCalls136.mask _ _ ⟨lowDom,highDom,blindDom,alphaDom⟩)
  · intro mask returned
    rw [NMT_CallTree.run_result,NMT_CallTree.erase_invoke] at returned
    rw [source.mask] at returned
    have maskDom := NNG_ProjectMaskDomain.returned fallback claims alpha mask lowDom highDom blindDom alphaDom returned
    exact NNG_DomRecord25_136.record25 fallback c env source s p prefixEq running terminal mask alpha claims t1 etaDom terminalDom maskDom
#print axioms mask
end AspisR1.NNG_DomMask136
