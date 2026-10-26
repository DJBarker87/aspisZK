import RPz7_PAln_ViewCuts
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.PAln_Physical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open MultiproofConeCanonical OraclePortCompactDraft

theorem state_bytes (s : Array U8 32#usize) : bytes (decodeState s)=bytesOf s.val := by
  apply List.ext_getElem
  · simp only [bytes,List.length_ofFn,bytesOf,List.length_map,s.property]
    scalar_tac
  · intro i hi hj
    simp only [bytes,List.getElem_ofFn,decodeState,bytesOf,List.getElem_map]

theorem range_bytes (proof out : Slice U8) (start stop : Usize)
    (h : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start:=start,«end»:=stop}=ok out) :
    bytesOf out.val=slice (bytesOf proof.val) start.val (stop.val-start.val) := by
  rw [PSem_Slices.range_bytes proof out start stop h]
  simp only [bytesOf,List.map_take,List.map_drop,slice]

theorem opening_sections (proof semantic y1 : Slice U8) (view : AspisR1SelectedWideViewV1.verifier.View)
    (accepted : AspisR1SelectedWideViewV1.verifier.candidate.wide_view proof semantic y1=ok (.Ok view)) :
    bytesOf view.round0.val=slice (bytesOf proof.val) 7527 224 ∧
    bytesOf view.round1.val=slice (bytesOf proof.val) 7783 224 ∧
    bytesOf view.final_message.val=slice (bytesOf proof.val) 8007 2048 := by
  obtain ⟨inactive,rootBytes,rootResult,root,hi,hp,h0,hr,hconvert,hunwrap,rootEq,h1,hf⟩ :=
    PAln_ViewCuts.selected proof semantic y1 view accepted
  have a : (7527#usize).val=7527 := by scalar_tac
  have b : (7751#usize).val=7751 := by scalar_tac
  have c : (7783#usize).val=7783 := by scalar_tac
  have d : (8007#usize).val=8007 := by scalar_tac
  have e : (10055#usize).val=10055 := by scalar_tac
  have first := range_bytes proof view.round0 7527#usize 7751#usize h0
  have second := range_bytes proof view.round1 7783#usize 8007#usize h1
  have last := range_bytes proof view.final_message 8007#usize 10055#usize hf
  exact ⟨by simpa only [a,b] using first,by simpa only [c,d] using second,
    by simpa only [d,e] using last⟩


#print axioms state_bytes
#print axioms range_bytes
#print axioms opening_sections
end AspisR1.PAln_Physical
