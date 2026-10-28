import NDO_JGl_InternalMaps
import RPv_FJh_M31DotSevenExact
import NDO_JGj_InternalRoundTotal
import RPv_FJh_InternalPairValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGl_InternalPairTotal
open Aeneas Aeneas.Std Result FIq_Native
open FJh_Base (State QM Decode)
open FIw_ArrayValue (canonical decoded)

theorem source (s l : State) (hs : canonical s) (hl : canonical l) :
    ∃ out : State, state_only_poseidon.interpolated_internal_pair s l=ok out ∧
      canonical out ∧ decoded out=R0P.poseidonInterpolatedInternalPair (decoded s) (decoded l) := by
  obtain ⟨w,rw,cw⟩ := JGl_InternalMaps.weights l hl
  obtain ⟨e,re,ce⟩ := JGl_InternalMaps.constants false
  obtain ⟨o,ro,co⟩ := JGl_InternalMaps.constants true
  obtain ⟨even,reven,ceven,_⟩ := FJh_M31DotSevenExact.source_success
    (Array.to_slice w) (Array.to_slice e) w.property e.property
    (by intro i hi; exact cw _ (List.getElem_mem hi))
    (by intro i hi; exact ce _ (List.getElem_mem hi))
  obtain ⟨odd,rodd,codd,_⟩ := FJh_M31DotSevenExact.source_success
    (Array.to_slice w) (Array.to_slice o) w.property o.property
    (by intro i hi; exact cw _ (List.getElem_mem hi))
    (by intro i hi; exact co _ (List.getElem_mem hi))
  obtain ⟨mid,rm,cm⟩ := JGj_InternalRoundTotal.source s even hs ceven
  obtain ⟨out,rf,cf⟩ := JGj_InternalRoundTotal.source mid odd cm codd
  have run : state_only_poseidon.interpolated_internal_pair s l=ok out := by
    unfold state_only_poseidon.interpolated_internal_pair
    simp only [show FIq_Native.core.array.Array.map FJh_InternalConstantCalls.even FJh_InternalWeights.rows ()=ok e from re,
      show FIq_Native.core.array.Array.map FJh_InternalConstantCalls.odd FJh_InternalWeights.rows ()=ok o from ro,
      rw,lift,bind_tc_ok,reven,rodd,rm,rf]
  exact ⟨out,run,FJh_InternalPairValue.value s l out hs hl run⟩
#print axioms source
end AspisR1.JGl_InternalPairTotal
end
