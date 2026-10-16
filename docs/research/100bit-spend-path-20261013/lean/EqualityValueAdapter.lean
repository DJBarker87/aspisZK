import EqualityValueSlice
import ExtractedMaskTowerAdd
import ExtractedMaskQM31Exact
import ExtractedMaskConstants

set_option autoImplicit false

namespace AspisR1.EqualityValueAdapter
open Aeneas.Std Result

abbrev QM := AspisR1.ExtractedMaskQM31Exact.CurrentQM
abbrev ExactQM := AspisR1.ExtractedMaskQM31Exact.QM31Exact
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM

def decode (x : QM) : ExactQM := AspisR1.ExtractedMaskQM31Exact.decode x

def factor (a b : ExactQM) : ExactQM := 1 - a - b + a * b + a * b

theorem current_qm_sub_mod (x y : QM)
    (hx : Canonical x) (hy : Canonical y) :
    ∃ z, AspisR1SelectedMaskProbe.field.QM31.sub x y = .ok z ∧
      Canonical z ∧
      AspisR1.ExtractedMaskTowerAdd.wordsQM z =
        (((x.c0.a.val + AspisR1.ExtractedMaskTowerAdd.P - y.c0.a.val) %
            AspisR1.ExtractedMaskTowerAdd.P,
          (x.c0.b.val + AspisR1.ExtractedMaskTowerAdd.P - y.c0.b.val) %
            AspisR1.ExtractedMaskTowerAdd.P),
         ((x.c1.a.val + AspisR1.ExtractedMaskTowerAdd.P - y.c1.a.val) %
            AspisR1.ExtractedMaskTowerAdd.P,
          (x.c1.b.val + AspisR1.ExtractedMaskTowerAdd.P - y.c1.b.val) %
            AspisR1.ExtractedMaskTowerAdd.P)) := by
  obtain ⟨a, ea, ca, va, vb⟩ :=
    AspisR1.ExtractedMaskTowerAdd.current_cm_sub_mod x.c0 y.c0 hx.1 hy.1
  obtain ⟨b, eb, cb, vc, vd⟩ :=
    AspisR1.ExtractedMaskTowerAdd.current_cm_sub_mod x.c1 y.c1 hx.2 hy.2
  refine ⟨⟨a, b⟩, ?_, ⟨ca, cb⟩, ?_⟩
  · simp only [AspisR1SelectedMaskProbe.field.QM31.sub, ea, eb, bind_tc_ok]
  · exact Prod.ext (Prod.ext va vb) (Prod.ext vc vd)

theorem current_qm_sub_exact (x y : QM)
    (hx : Canonical x) (hy : Canonical y) :
    ∃ z, AspisR1SelectedMaskProbe.field.QM31.sub x y = .ok z ∧
      Canonical z ∧ decode z = decode x - decode y := by
  obtain ⟨z, hz, hcanon, hwords⟩ := current_qm_sub_mod x y hx hy
  refine ⟨z, hz, hcanon, ?_⟩
  change AspisV8R17.QM31WordTower.decodeQ
      (AspisR1.ExtractedMaskQM31Mul.wordsQM z) =
    AspisV8R17.QM31WordTower.decodeQ
        (AspisR1.ExtractedMaskQM31Mul.wordsQM x) -
      AspisV8R17.QM31WordTower.decodeQ
        (AspisR1.ExtractedMaskQM31Mul.wordsQM y)
  have hword :
      AspisR1.ExtractedMaskQM31Mul.wordsQM z =
        AspisV8R17.GeneratedQM31Linear.qmSubWords
          (AspisR1.ExtractedMaskQM31Mul.wordsQM x)
          (AspisR1.ExtractedMaskQM31Mul.wordsQM y) := by
    exact hwords
  rw [hword]
  exact AspisV8R17.QM31WordTower.decode_sub _ _ (by exact hy)

/-- The extracted closure's algebraic factor, with each current operation
kept explicit in the success result and canonicality chain. -/
theorem equality_factor_call (a b : QM)
    (ha : Canonical a) (hb : Canonical b) :
    ∃ z,
      AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.equality_value.closure.Insts.CoreOpsFunctionFnPairQM31QM31QM31.call
        () (a, b) = .ok z ∧
      Canonical z ∧ decode z = factor (decode a) (decode b) := by
  obtain ⟨ab, hab, habcan, habval⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact a b ha hb
  obtain ⟨q, hq, hqcan, hqval⟩ :=
    current_qm_sub_exact AspisR1SelectedMaskProbe.field.QM31.ONE a
      (AspisR1.ExtractedMaskConstants.one_canonical) ha
  obtain ⟨q1, hq1, hq1can, hq1val⟩ := current_qm_sub_exact q b hqcan hb
  obtain ⟨q2, hq2, hq2can, hq2val⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact q1 ab hq1can habcan
  obtain ⟨q3, hq3, hq3can, hq3val⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact q2 ab hq2can habcan
  have hqval' : AspisR1.ExtractedMaskQM31Exact.decode q =
      AspisR1.ExtractedMaskQM31Exact.decode AspisR1SelectedMaskProbe.field.QM31.ONE -
        AspisR1.ExtractedMaskQM31Exact.decode a := by
    exact hqval
  have hq1val' : AspisR1.ExtractedMaskQM31Exact.decode q1 =
      AspisR1.ExtractedMaskQM31Exact.decode q -
        AspisR1.ExtractedMaskQM31Exact.decode b := by
    exact hq1val
  refine ⟨q3, ?_, hq3can, ?_⟩
  · simp only [AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.equality_value.closure.Insts.CoreOpsFunctionFnPairQM31QM31QM31.call,
      hab, hq, hq1, hq2, hq3, bind_tc_ok]
  · change decode q3 = factor (decode a) (decode b)
    dsimp [factor]
    change AspisR1.ExtractedMaskQM31Exact.decode q3 =
      1 - AspisR1.ExtractedMaskQM31Exact.decode a -
        AspisR1.ExtractedMaskQM31Exact.decode b +
        AspisR1.ExtractedMaskQM31Exact.decode a *
          AspisR1.ExtractedMaskQM31Exact.decode b +
        AspisR1.ExtractedMaskQM31Exact.decode a *
          AspisR1.ExtractedMaskQM31Exact.decode b
    rw [hq3val, hq2val, hq1val', hqval', habval,
      AspisR1.ExtractedMaskConstants.one_decode]

#print axioms current_qm_sub_mod
#print axioms current_qm_sub_exact
#print axioms equality_factor_call

end AspisR1.EqualityValueAdapter
