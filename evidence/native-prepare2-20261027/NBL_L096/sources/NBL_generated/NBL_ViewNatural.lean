import NBL_ViewProduct
set_option autoImplicit false
namespace AspisR1.NBL_ViewNatural
open Aeneas Aeneas.Std Result AspisR1SelectedWideViewV1
open AspisR1.StrictWideByteCodec AspisR1.UnrolledWideByteReads

def bytes (proof : Slice U8) (size : 10055≤proof.val.length) : Array U8 32#usize :=
  ⟨(NBL_SlicePort.segment proof 7495#usize 7527#usize).val,by
    have len := NBL_SlicePort.length proof 7495#usize 7527#usize
      (by decide) (by change 7527≤_;omega)
    exact len⟩

def decoded (proof : Slice U8) (size : 10055≤proof.val.length) :
    Option aspis_core.field.wide_exact.WideExact :=
  (decodeWideLE (arrayBytes32 (bytes proof size))).map
    (fun value => parserCarrier (CandidateWideParserRefinement.limbsToCandidate value))

/-- Exact all-byte inactive decoder into the SELECTED nominal carrier. -/
theorem parser (proof : Slice U8) (size : 10055≤proof.val.length) :
    viewFromBytes (NBL_SlicePort.segment proof 7495#usize 7527#usize)=ok (decoded proof size) := by
  have same : Array.to_slice (bytes proof size)=NBL_SlicePort.segment proof 7495#usize 7527#usize := rfl
  unfold viewFromBytes
  rw [←same,UnrolledWideParserRefinement.source_refines,bind_tc_ok]
  simp only [decoded,Option.map_map,Function.comp_def]

/-- Whole selected View/Parse Result from frozen proof bytes, with NO supplied
parser output, successful View, canonicality or selected field premise. -/
theorem source (proof semantic y1 : Slice U8) (size : 10055≤proof.val.length) :
    verifier.candidate.wide_view proof semantic y1=
      ok (NBL_ViewProduct.product proof semantic y1 size (decoded proof size)) :=
  NBL_ViewProduct.source proof semantic y1 size (decoded proof size) (parser proof size)

#print axioms parser
#print axioms source
end AspisR1.NBL_ViewNatural
