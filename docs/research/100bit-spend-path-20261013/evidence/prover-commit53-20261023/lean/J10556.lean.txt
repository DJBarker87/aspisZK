import R1Z.ProverCommitWeightsMaterialBinding53
import R1Z.ProverCommitMaterialCaller49
/-! Complete stored constructor and materialization caller. The object is
constructed once; no raw-table or factor-model image is assumed. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitWeightsMaterial53
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitWideOps48 ProverCommitMix48
open ProverCommitValueRange47 (embed)
open ProverCommitSuccessorPoint49 (decoded)
open AspisR1.ExtractedCurrentQM31Exact (decode)
open ProverCommitWeightsStorage53 (State)
open scoped BigOperators

variable (p : Nat → Old.Q) (hp : ∀ i, i<10 → Canonical (p i))
    (x0 y0 x1 y1 : Old.Q) (hx0 : Canonical x0) (hy0 : Canonical y0)
    (hx1 : Canonical x1) (hy1 : Canonical y1)

def st : State := Classical.choose (ProverCommitWeights53.exact_result p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1)

theorem st_spec :
    weights53.new (ProverCommitQArray48.array 10#usize p) (ProverCommitNativeQ48.source x0)
      (ProverCommitNativeQ48.source y0) (ProverCommitNativeQ48.source x1) (ProverCommitNativeQ48.source y1)=
      ok (st p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1) ∧
    ∀ (j : Usize) (hj : j.val<1024), ∃ out : Nat → Old.Q,
      weights53.row (st p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1) j=ok (ProverCommitQArray48.array 7#usize out) ∧
      (∀ k, k<7 → Canonical (out k)) ∧
      ∀ k : Fin 7, decode (out k.val)=ProverCommitRawSource49.model (decoded p)
        (decode x0) (decode y0) (decode x1) (decode y1) ⟨j.val,hj⟩ k :=
  Classical.choose_spec (ProverCommitWeights53.exact_result p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1)

def row (j : Fin 1024) : Nat → Old.Q :=
  Classical.choose ((st_spec p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1).2 (ProverCommitMaterialCaller49.index j) j.isLt)

def raw (j k : Nat) : Old.Q :=
  if h : j<1024 then row p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1 ⟨j,h⟩ k else zero

theorem row_spec (j : Fin 1024) :
    weights53.row (st p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1) (ProverCommitMaterialCaller49.index j)=
      ok (ProverCommitQArray48.array 7#usize (raw p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1 j.val)) ∧
    (∀ k, k<7 → Canonical (raw p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1 j.val k)) ∧
    ∀ k : Fin 7, decode (raw p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1 j.val k.val)=
      ProverCommitRawSource49.model (decoded p) (decode x0) (decode y0) (decode x1) (decode y1) j k := by
  have hraw : raw p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1 j.val=
      row p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1 j := by
    funext k
    simp only [raw,dif_pos j.isLt]
  rw [hraw]
  exact Classical.choose_spec ((st_spec p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1).2
    (ProverCommitMaterialCaller49.index j) j.isLt)

theorem source_row (j : Usize) (hj : j.val<1024) :
    weights53.row (st p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1) j=
      ok (ProverCommitQArray48.array 7#usize (raw p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1 j.val)) := by
  have hi : ProverCommitMaterialCaller49.index ⟨j.val,hj⟩=j := by
    apply UScalar.eq_of_val_eq
    rfl
  have hs := (row_spec p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1 ⟨j.val,hj⟩).1
  rw [hi] at hs
  exact hs

def run (point : Array field.QM31 10#usize) (a b c d : field.QM31) (x : Source) :
    Result (Array Source 1024#usize) := do
  let state ← weights53.new point a b c d
  ProverCommitWeightsMaterialBinding53.run state x

theorem exact_result (kappa : Raw) (hk : canonical kappa) :
    ∃ out : Nat → Raw,
      run (ProverCommitQArray48.array 10#usize p) (ProverCommitNativeQ48.source x0)
        (ProverCommitNativeQ48.source y0) (ProverCommitNativeQ48.source x1) (ProverCommitNativeQ48.source y1)
        (source kappa)=ok (sourceArray 1024#usize out) ∧
      (∀ i, i<1024 → canonical (out i)) ∧
      ∀ j : Fin 1024, value (out j.val)=∑ k : Fin 7, value kappa^k.val*ProverCommitWideRows49.rows
        (fun i => embed (decoded p i)) (embed (decode x0)) (embed (decode y0))
        (embed (decode x1)) (embed (decode y1)) j k := by
  obtain ⟨out,hout,hcout,hdout⟩ := ProverCommitMaterialOutput49.kappa_all kappa hk
    (raw p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1)
  refine ⟨out,?_,hcout,?_⟩
  · simp only [run,(st_spec p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1).1,bind_tc_ok]
    rw [ProverCommitWeightsMaterialBinding53.run_eq _ _ (source_row p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1)]
    exact hout
  · intro j
    rw [hdout j]
    apply Finset.sum_congr rfl
    intro k hmem
    rw [(row_spec p hp x0 y0 x1 y1 hx0 hy0 hx1 hy1 j).2.2 k]
    change value kappa^k.val*embed (ProverCommitRawSource49.model (decoded p)
      (decode x0) (decode y0) (decode x1) (decode y1) j k)=_
    rw [ProverCommitWideRows49.embed_rows]

#print axioms st_spec
#print axioms row_spec
#print axioms source_row
#print axioms exact_result
end R1Z.ProverCommitWeightsMaterial53
