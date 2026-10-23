import AspisR1ProducerRelease47.EncoderLeaf54
import R1Z.ProverCommitEncoderChannels54
import R1Z.ProverCommitEncoderPhi53
/-! Complete owned encoder at supplied canonical nodes and fibre coordinates.
The exact native nodes_for/domain point provenance is a separate obligation. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitEncoderLeaf54
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitWideOps48 ProverCommitMix48 ProverCommitEncoderEval54
attribute [local irreducible] source value sourceArray eval

theorem exact_result (f : Nat → Raw) (hf : ∀ i, i<1024 → canonical (f i))
    (p : Nat → U32) (hp : ∀ i, i<9 → (p i).val<2147483647)
    (x y : Raw) (hx : canonical x) (hy : canonical y) :
    ∃ out : Nat → Raw,
      encoder54.encode_with_nodes (sourceArray 1024#usize f) (nodes p) (source x) (source y)=
        ok (sourceArray 4#usize out) ∧
      (∀ s, s<4 → canonical (out s)) ∧
      ∀ s : Fin 4, value (out s.val)=ProverCommitEncoderPhi53.phi (value x) (value y)
        (fun s => eval 8 (fun i => value (f (4*i+s.val))) (fun i => value (base (p i))) 0) s := by
  obtain ⟨h,hh,hch,hdh⟩ := ProverCommitEncoderChannels54.exact_result f hf p hp
  obtain ⟨out,hout,hcout,hdout⟩ := ProverCommitEncoderPhi53.exact_result x y hx hy h hch
  refine ⟨out,?_,hcout,?_⟩
  · rw [encoder54.encode_with_nodes,hh]
    simp only [bind_tc_ok]
    exact hout
  · intro s
    rw [hdout s]
    have he : (fun i : Fin 4 => value (h i.val))=
        (fun s : Fin 4 => eval 8 (fun i => value (f (4*i+s.val)))
          (fun i => value (base (p i))) 0) := funext hdh
    rw [he]

#print axioms exact_result
end R1Z.ProverCommitEncoderLeaf54
