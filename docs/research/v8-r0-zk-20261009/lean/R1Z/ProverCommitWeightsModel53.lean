import R1Z.ProverCommitWeightsMaterial53
/-! Stored construction connected to the R1 challenge carrier. The remaining
hypotheses describe only decoding of caller inputs, never producer outputs. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitWeightsModel53
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitWideOps48 ProverCommitMix48
open ProverCommitValueRange47 (embed)
open ProverCommitSuccessorPoint49 (decoded)
open AspisR1.ExtractedCurrentQM31Exact (decode)
open scoped BigOperators

theorem exact_result (p : Nat → Old.Q) (hp : ∀ i, i<10 → Canonical (p i))
    (x0 y0 x1 y1 : Old.Q) (hx0 : Canonical x0) (hy0 : Canonical y0)
    (hx1 : Canonical x1) (hy1 : Canonical y1) (k : Raw) (hk : canonical k)
    (ch : R0Z.HonestView.Challenges Exact)
    (ha : (fun i => embed (decoded p i))=R0Z.HonestView.alpha ch)
    (hz0x : embed (decode x0)=(ch.circle 0).1.1)
    (hz0y : embed (decode y0)=(ch.circle 0).1.2)
    (hz1x : embed (decode x1)=(ch.circle 1).1.1)
    (hz1y : embed (decode y1)=(ch.circle 1).1.2)
    (hkch : value k=ch.opening 1) :
    ∃ out : Nat → Raw,
      ProverCommitWeightsMaterial53.run (ProverCommitQArray48.array 10#usize p)
        (ProverCommitNativeQ48.source x0) (ProverCommitNativeQ48.source y0)
        (ProverCommitNativeQ48.source x1) (ProverCommitNativeQ48.source y1) (source k)=
        ok (sourceArray 1024#usize out) ∧
      (∀ i, i<1024 → canonical (out i)) ∧
      ∀ j : Fin 1024, value (out j.val)=Batched.weightsR1 AspisR1.rowEquiv ch j := by
  obtain ⟨out,hr,hc,hd⟩ := ProverCommitWeightsMaterial53.exact_result p hp x0 y0 x1 y1
    hx0 hy0 hx1 hy1 k hk
  refine ⟨out,hr,hc,?_⟩
  intro j
  rw [hd j,ha,hz0x,hz0y,hz1x,hz1y,hkch]
  exact ProverCommitWideRows49.weighted_rows ch j

#print axioms exact_result
end R1Z.ProverCommitWeightsModel53
