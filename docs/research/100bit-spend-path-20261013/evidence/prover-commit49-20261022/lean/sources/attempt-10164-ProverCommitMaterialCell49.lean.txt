import R1Z.ProverCommitWideRows49
import R1Z.ProverCommitWeightOutput49
/-! Complete raw helper values and kappa producer feed one materialized cell.
The R1 adapter exposes only representation equations for caller inputs. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitMaterialCell49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitWideOps48
open ProverCommitValueRange47 (embed)
open AspisR1.ExtractedCurrentQM31Exact (decode)
open ProverCommitSuccessorPoint49 (decoded)
open scoped BigOperators

def run (p : Array field.QM31 10#usize) (x0 y0 x1 y1 : field.QM31) (kappa : Source) (j : Usize) : Result Source := do
  let raw ← ProverCommitRawSource49.run p x0 y0 x1 y1 j
  ProverCommitWeightOutput49.cell raw kappa

theorem cell_value (p : Nat → Old.Q) (hp : ∀ i, i<10 → Canonical (p i))
    (x0 y0 x1 y1 : Old.Q) (hx0 : Canonical x0) (hy0 : Canonical y0)
    (hx1 : Canonical x1) (hy1 : Canonical y1) (kappa : Raw) (hk : canonical kappa)
    (j : Usize) (hj : j.val<1024) :
    ∃ z : Raw, run (ProverCommitQArray48.array 10#usize p) (ProverCommitNativeQ48.source x0)
      (ProverCommitNativeQ48.source y0) (ProverCommitNativeQ48.source x1) (ProverCommitNativeQ48.source y1) (source kappa) j=ok (source z) ∧
      canonical z ∧ value z=∑ k : Fin 7, value kappa^k.val*ProverCommitWideRows49.rows
        (fun i => embed (decoded p i)) (embed (decode x0)) (embed (decode y0))
        (embed (decode x1)) (embed (decode y1)) ⟨j.val,hj⟩ k := by
  obtain ⟨raw,hraw,hcraw,hd⟩ := ProverCommitRawSource49.exact_result p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1 j hj
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitWeightOutput49.cell_exact raw kappa hk
  refine ⟨z,?_,hcz,?_⟩
  · simp only [run,hraw,hz,bind_tc_ok]
  · rw [hdz]
    apply Finset.sum_congr rfl
    intro k hmem
    rw [hd k]
    change value kappa^k.val*embed (ProverCommitRawSource49.model (decoded p) (decode x0) (decode y0) (decode x1) (decode y1) ⟨j.val,hj⟩ k)=_
    rw [ProverCommitWideRows49.embed_rows]

theorem cell_model (p : Nat → Old.Q) (hp : ∀ i, i<10 → Canonical (p i))
    (x0 y0 x1 y1 : Old.Q) (hx0 : Canonical x0) (hy0 : Canonical y0)
    (hx1 : Canonical x1) (hy1 : Canonical y1) (kappa : Raw) (hk : canonical kappa)
    (ch : R0Z.HonestView.Challenges ProverCommitValueRange47.E)
    (hpa : (fun i => embed (decoded p i))=R0Z.HonestView.alpha ch)
    (hkappa : value kappa=ch.opening 1)
    (hz0x : embed (decode x0)=(ch.circle 0).1.1) (hz0y : embed (decode y0)=(ch.circle 0).1.2)
    (hz1x : embed (decode x1)=(ch.circle 1).1.1) (hz1y : embed (decode y1)=(ch.circle 1).1.2)
    (j : Usize) (hj : j.val<1024) :
    ∃ z : Raw, run (ProverCommitQArray48.array 10#usize p) (ProverCommitNativeQ48.source x0)
      (ProverCommitNativeQ48.source y0) (ProverCommitNativeQ48.source x1) (ProverCommitNativeQ48.source y1) (source kappa) j=ok (source z) ∧
      canonical z ∧ value z=R1Z.Batched.weightsR1 AspisR1.rowEquiv ch ⟨j.val,hj⟩ := by
  obtain ⟨z,hz,hcz,hdz⟩ := cell_value p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1 kappa hk j hj
  refine ⟨z,hz,hcz,?_⟩
  rw [hpa,hkappa,hz0x,hz0y,hz1x,hz1y] at hdz
  exact hdz.trans (ProverCommitWideRows49.weighted_rows ch ⟨j.val,hj⟩)

#print axioms cell_value
#print axioms cell_model
end R1Z.ProverCommitMaterialCell49
