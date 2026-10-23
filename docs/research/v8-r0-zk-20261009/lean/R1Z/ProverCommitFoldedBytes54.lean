import R1Z.ProverCommitFoldedValues54
import R1Z.ProverCommitOpeningBytes49
import R1Z.PhaseLeafEncodingBin
/-! The complete ordered 128-byte folded-leaf image after source evaluation.
This uses the retained canonical byte codec; native byte/caller binding is separate. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitFoldedBytes54
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitWideOps48 ProverCommitMix48 ProverCommitOpeningBytes49

theorem model_stream (f : Fin 4 → Exact) : modelStream 4 f=
    (AspisR1.FoldedLeafCodec.encodeFolded f).map UInt8.ofFin := by
  simp only [modelStream,AspisR1.FoldedLeafCodec.encodeFolded,AspisR1.FixedWidthDecoder.encode,
    List.flatMap_def,List.map_flatten,List.map_map,List.map_ofFn,Function.comp_def,
    AspisR1.FoldedLeafCodec.encodeWide]
  unfold ProverCommitValueRange47.bytes
  rfl

theorem exact_result (f : Nat → Raw) (hf : ∀ i, i<256 → canonical (f i))
    (v : Usize) (u : Fin 65536) (hv : v.val=u.val) :
    ∃ (out : Nat → Raw) (hcout : ∀ s, s<4 → canonical (out s)),
      leaves54.folded_values (sourceArray 256#usize f) v=ok (sourceArray 4#usize out) ∧
      stream 4 out hcout=PhaseLeafEncodingBin.foldedLeaf (fun i => value (f i.val))
        ⟨u.val,by have := u.isLt;omega⟩ := by
  obtain ⟨out,hout,hcout,hdout⟩ := ProverCommitFoldedValues54.exact_result f hf v u hv
  refine ⟨out,hcout,hout,?_⟩
  rw [stream_image 4 out hcout _ hdout,model_stream]
  rw [PhaseLeafEncodingBin.foldedLeaf,dif_pos (by exact u.isLt)]
  rfl

#print axioms model_stream
#print axioms exact_result
end R1Z.ProverCommitFoldedBytes54
