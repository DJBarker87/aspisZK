import R1Z.ProverCommitOpeningModel53
import R1Z.ProverCommitFoldedBytes54
/-! Compose the complete retained opening producer with the folded-leaf owner.
The leaf coefficients are derived from q1, not an assumed model array. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitOpeningFolded54
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitWideOps48 ProverCommitMix48
open ProverCommitValueRange47 (embed)
open ProverCommitSuccessorPoint49 (decoded)
open AspisR1.ExtractedCurrentQM31Exact (decode)
variable (c : Nat → Nat → Old.Q) (hc : ∀ l, l<29 → ∀ i, i<1024 → Canonical (c l i))

def run (p : Array field.QM31 10#usize) (x0 y0 x1 y1 : field.QM31) (g k a b : Source) (v : Usize) := do
  let r ← ProverCommitOpeningModel53.run c hc p x0 y0 x1 y1 g k a b
  let leaf ← leaves54.folded_values r.2.1 v
  ok (r,leaf)

attribute [local irreducible] source value sourceArray

theorem exact_result (p : Nat → Old.Q) (hp : ∀ i, i<10 → Canonical (p i))
    (x0 y0 x1 y1 : Old.Q) (hx0 : Canonical x0) (hy0 : Canonical y0)
    (hx1 : Canonical x1) (hy1 : Canonical y1) (g k a b : Raw)
    (hg : canonical g) (hk : canonical k) (hca : canonical a) (hcb : canonical b)
    (ch : R0Z.HonestView.Challenges Exact)
    (hpoint : (fun i => embed (decoded p i))=R0Z.HonestView.alpha ch)
    (hz0x : embed (decode x0)=(ch.circle 0).1.1)
    (hz0y : embed (decode y0)=(ch.circle 0).1.2)
    (hz1x : embed (decode x1)=(ch.circle 1).1.1)
    (hz1y : embed (decode y1)=(ch.circle 1).1.2)
    (hgch : value g=ch.opening 0) (hkch : value k=ch.opening 1)
    (hach : value a=ch.opening 2) (hbch : value b=ch.opening 3)
    (v : Usize) (u : Fin 65536) (hv : v.val=u.val) :
    ∃ (c0 q1 c1 fin leaf : Nat → Raw) (hcleaf : ∀ s, s<4 → canonical (leaf s)),
      run c hc (ProverCommitQArray48.array 10#usize p)
        (ProverCommitNativeQ48.source x0) (ProverCommitNativeQ48.source y0)
        (ProverCommitNativeQ48.source x1) (ProverCommitNativeQ48.source y1)
        (source g) (source k) (source a) (source b) v=
        ok ((List.ofFn (fun i : Fin 7 => source (c0 i.val)),sourceArray 256#usize q1,
          List.ofFn (fun i : Fin 7 => source (c1 i.val)),sourceArray 64#usize fin),sourceArray 4#usize leaf) ∧
      ProverCommitOpeningBytes49.stream 4 leaf hcleaf=PhaseLeafEncodingBin.foldedLeaf
        (Batched.q1 AspisR1.rowEquiv ch (ProverCommitGammaCoefficients53.wideTrace c))
        ⟨u.val,by have := u.isLt;omega⟩ := by
  obtain ⟨c0,q1,w1,c1,fin,hrun,hcc,hcf,hcfin,hq1,hw1,hd0,hd1,hdf⟩ :=
    ProverCommitOpeningModel53.exact_result c hc p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1
      g k a b hg hk hca hcb ch hpoint hz0x hz0y hz1x hz1y hgch hkch hach hbch
  obtain ⟨leaf,hcleaf,hleaf,hbytes⟩ := ProverCommitFoldedBytes54.exact_result q1 (fun i hi => (hcf i hi).1) v u hv
  refine ⟨c0,q1,c1,fin,leaf,hcleaf,?_,?_⟩
  · simp only [run,hrun,bind_tc_ok,hleaf]
  · have he : (fun i : Fin 256 => value (q1 i.val))=
        Batched.q1 AspisR1.rowEquiv ch (ProverCommitGammaCoefficients53.wideTrace c) := by
      rw [ProverCommitOpeningModel53.q1_primal]
      exact funext hq1
    simpa only [he] using hbytes

#print axioms exact_result
end R1Z.ProverCommitOpeningFolded54
