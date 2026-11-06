import NKG_InternalMaps
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_InternalSource
open Aeneas Aeneas.Std Result FIq_Native
open FJh_Base (State QM P)
open FIw_ArrayValue (canonical decoded)
/-- SAME seven-selector maps, both fixed tables and both dot calls supply all
round domains; the intermediate canonical state comes from the first round. -/
theorem result (s l : State) (hs : canonical s) (hl : canonical l) :
 ∃ out,state_only_poseidon.interpolated_internal_pair s l=ok out ∧ canonical out ∧
 decoded out=R0P.poseidonInterpolatedInternalPair (decoded s) (decoded l) := by
 obtain ⟨w,rw,cw⟩ := NKG_InternalMaps.weights l hl
 obtain ⟨e,re,ce⟩ := NKG_InternalMaps.constants_even
 obtain ⟨o,ro,co⟩ := NKG_InternalMaps.constants_odd
 have wd : FJh_M31DotReads.CanonicalWeights (Array.to_slice w) := by
   intro i hi
   exact cw _ (List.getElem_mem _)
 have ed : FJh_M31DotReads.CanonicalValues (Array.to_slice e) := by
   intro i hi
   exact ce _ (List.getElem_mem _)
 have od : FJh_M31DotReads.CanonicalValues (Array.to_slice o) := by
   intro i hi
   exact co _ (List.getElem_mem _)
 have wl : (Array.to_slice w).val.length=7 := w.property
 have el : (Array.to_slice e).val.length=7 := e.property
 have ol : (Array.to_slice o).val.length=7 := o.property
 obtain ⟨even,reven,canonEven,_⟩ := NFT_DotSource.source (Array.to_slice w) (Array.to_slice e) wl el wd ed
 obtain ⟨odd,rodd,canonOdd,_⟩ := NFT_DotSource.source (Array.to_slice w) (Array.to_slice o) wl ol wd od
 obtain ⟨middle,rm,cm,_⟩ := NIH_InternalRound.result s even hs canonEven
 obtain ⟨out,rf,cf,_⟩ := NIH_InternalRound.result middle odd cm canonOdd
 have run : state_only_poseidon.interpolated_internal_pair s l=ok out := by
   simp only [state_only_poseidon.interpolated_internal_pair,rw,re,ro,lift,bind_tc_ok,reven,rodd,rm,rf]
 exact ⟨out,run,FJh_InternalPairValue.value s l out hs hl run⟩
#print result
#print axioms result
end AspisR1.NKG_InternalSource
end
