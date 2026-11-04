import NFT_Pack
set_option autoImplicit false
namespace NFT_PackWords
open Aeneas Aeneas.Std Result
open AspisR1.ExtractedMaskQmPackBase4Arithmetic
open AspisR1.ExtractedMaskQmPackBase4SourceArithmetic
open AspisR1.ExtractedMaskQmPackBase4Tail
open AspisR1.ExtractedMaskQmPackBase4Fragments

abbrev CurrentQM := AspisR1.ExtractedMaskQM31Exact.CurrentQM
abbrev CurrentCanonicalQM := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM

theorem tail (v : Fin 4 → CurrentQM) (hv : ∀ j, CurrentCanonicalQM (v j)) :
    ∃ out : CurrentQM, run v=ok out ∧ CurrentCanonicalQM out ∧
      out.c0.a.val=acc00 v%2147483647 ∧ out.c0.b.val=acc01 v%2147483647 ∧
      out.c1.a.val=acc10 v%2147483647 ∧ out.c1.b.val=acc11 v%2147483647 := by
  obtain ⟨raw00,raw01,raw10,raw11,h00,hv00,h01,hv01,h10,hv10,h11,hv11⟩:=source_accumulators_qm_limbs v hv
  obtain ⟨a,ra,va,ca⟩:=AspisR1.ExtractedMaskReducer.current_wrapper_mod raw00
  obtain ⟨b,rb,vb,cb⟩:=AspisR1.ExtractedMaskReducer.current_wrapper_mod raw01
  obtain ⟨c,rc,vc,cc⟩:=AspisR1.ExtractedMaskReducer.current_wrapper_mod raw10
  obtain ⟨d,rd,vd,cd⟩:=AspisR1.ExtractedMaskReducer.current_wrapper_mod raw11
  refine ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,?_,⟨⟨ca,cb⟩,⟨cc,cd⟩⟩,?_,?_,?_,?_⟩
  · rw [run_eq_factored]
    simp only [factored,h00,h01,h10,h11,ra,rb,rc,rd,AspisR1SelectedMaskProbe.field.CM31.new,bind_tc_ok]
  · simpa only [hv00] using va
  · simpa only [hv01] using vb
  · simpa only [hv10] using vc
  · simpa only [hv11] using vd

theorem source (values : Slice NFT_Pack.Q) (short : values.length≤4)
    (canonical : ∀ q ∈ values.val, NFT_Pack.Canonical q) :
    ∃ out : CurrentQM, AspisR1SelectedMaskProbe.field.qm31_pack_base4 values=ok out ∧
      CurrentCanonicalQM out ∧
      out.c0.a.val=acc00 (NFT_Pack.Whole (NFT_Pack.paddedSlice values short) (NFT_Pack.padded_length values short))%2147483647 ∧
      out.c0.b.val=acc01 (NFT_Pack.Whole (NFT_Pack.paddedSlice values short) (NFT_Pack.padded_length values short))%2147483647 ∧
      out.c1.a.val=acc10 (NFT_Pack.Whole (NFT_Pack.paddedSlice values short) (NFT_Pack.padded_length values short))%2147483647 ∧
      out.c1.b.val=acc11 (NFT_Pack.Whole (NFT_Pack.paddedSlice values short) (NFT_Pack.padded_length values short))%2147483647 := by
  rw [NFT_Pack.graph values short]
  exact tail _ (NFT_Pack.padded_canonical values short canonical)

#print axioms tail
#print axioms source
end NFT_PackWords
