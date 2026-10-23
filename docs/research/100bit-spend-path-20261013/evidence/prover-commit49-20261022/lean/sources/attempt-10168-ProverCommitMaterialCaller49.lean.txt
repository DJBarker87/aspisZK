import R1Z.ProverCommitMaterialCell49
import R1Z.ProverCommitMaterialOutput49
/-! Whole materialization values from raw rows constructed by the proved
producers, with every raw-source Result retained as a conclusion. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitMaterialCaller49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitWideOps48 ProverCommitMix48
open ProverCommitValueRange47 (embed)
open ProverCommitSuccessorPoint49 (decoded)
open AspisR1.ExtractedCurrentQM31Exact (decode)
open scoped BigOperators

variable (p : Nat → Old.Q) (hp : ∀ i, i<10 → Canonical (p i))
    (x0 y0 x1 y1 : Old.Q) (hx0 : Canonical x0) (hy0 : Canonical y0)
    (hx1 : Canonical x1) (hy1 : Canonical y1)

def index (j : Fin 1024) : Usize := UScalar.ofNatCore j.val
  (by have hs := ProverCommitPairCounter47.usize_large;rw [UScalar.size_def] at hs;have := j.isLt;omega)

def row (j : Fin 1024) : Nat → Old.Q :=
  Classical.choose (ProverCommitRawSource49.exact_result p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1 (index j) j.isLt)

def raw (j : Nat) : Nat → Old.Q := if h : j<1024 then row p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1 ⟨j,h⟩
  else fun _ => zero

theorem raw_spec (j : Fin 1024) :
    ProverCommitRawSource49.run (ProverCommitQArray48.array 10#usize p) (ProverCommitNativeQ48.source x0)
      (ProverCommitNativeQ48.source y0) (ProverCommitNativeQ48.source x1) (ProverCommitNativeQ48.source y1) (index j)=
      ok (ProverCommitQArray48.array 7#usize (raw p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1 j.val)) ∧
    (∀ k, k<7 → Canonical (raw p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1 j.val k)) ∧
    ∀ k : Fin 7, decode (raw p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1 j.val k.val)=
      ProverCommitRawSource49.model (decoded p) (decode x0) (decode y0) (decode x1) (decode y1) j k := by
  rw [raw,dif_pos j.isLt]
  exact Classical.choose_spec (ProverCommitRawSource49.exact_result p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1 (index j) j.isLt)

theorem material_values (kappa : Raw) (hk : canonical kappa) :
    ∃ out : Nat → Raw,
      ProverCommitMaterialOutput49.run (source kappa) (ProverCommitMaterialFill49.table
        (raw p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1))=ok (sourceArray 1024#usize out) ∧
      (∀ i, i<1024 → canonical (out i)) ∧
      ∀ j : Fin 1024, value (out j.val)=∑ k : Fin 7, value kappa^k.val*ProverCommitWideRows49.rows
        (fun i => embed (decoded p i)) (embed (decode x0)) (embed (decode y0))
        (embed (decode x1)) (embed (decode y1)) j k := by
  obtain ⟨out,hout,hcout,hdout⟩ := ProverCommitMaterialOutput49.kappa_all kappa hk
    (raw p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1)
  refine ⟨out,hout,hcout,?_⟩
  intro j
  rw [hdout j]
  apply Finset.sum_congr rfl
  intro k hmem
  rw [(raw_spec p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1 j).2.2 k]
  change value kappa^k.val*embed (ProverCommitRawSource49.model (decoded p)
    (decode x0) (decode y0) (decode x1) (decode y1) j k)=_
  rw [ProverCommitWideRows49.embed_rows]

theorem material_model (kappa : Raw) (hk : canonical kappa)
    (ch : R0Z.HonestView.Challenges ProverCommitValueRange47.E)
    (hpa : (fun i => embed (decoded p i))=R0Z.HonestView.alpha ch)
    (hkappa : value kappa=ch.opening 1)
    (hz0x : embed (decode x0)=(ch.circle 0).1.1) (hz0y : embed (decode y0)=(ch.circle 0).1.2)
    (hz1x : embed (decode x1)=(ch.circle 1).1.1) (hz1y : embed (decode y1)=(ch.circle 1).1.2) :
    ∃ out : Nat → Raw,
      ProverCommitMaterialOutput49.run (source kappa) (ProverCommitMaterialFill49.table
        (raw p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1))=ok (sourceArray 1024#usize out) ∧
      (∀ i, i<1024 → canonical (out i)) ∧
      ∀ j : Fin 1024, value (out j.val)=R1Z.Batched.weightsR1 AspisR1.rowEquiv ch j := by
  obtain ⟨out,hout,hcout,hdout⟩ := material_values p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1 kappa hk
  refine ⟨out,hout,hcout,?_⟩
  intro j
  rw [hpa,hkappa,hz0x,hz0y,hz1x,hz1y] at hdout
  exact (hdout j).trans (ProverCommitWideRows49.weighted_rows ch j)

#print axioms raw_spec
#print axioms material_values
#print axioms material_model
end R1Z.ProverCommitMaterialCaller49
