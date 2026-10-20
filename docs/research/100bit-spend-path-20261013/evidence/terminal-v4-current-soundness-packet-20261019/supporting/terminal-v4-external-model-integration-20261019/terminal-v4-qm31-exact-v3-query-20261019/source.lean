import TerminalV4QM31TowerV1
import TerminalV4TowerSubV1
import AspisV8R15.ExactTowerBase

/-!
Exact-tower view of the current extracted QM31 coordinates. This adapts the
already-proved current-operation adapter to the retained exact quadratic tower;
it does not add source-correspondence claims.
-/
set_option autoImplicit false

namespace AspisR1.TerminalV4QM31Exact

abbrev CurrentQM := AspisR1.TerminalV4QM31Tower.CurrentQM
abbrev CurrentCanonicalQM := AspisR1.TerminalV4QM31Tower.CurrentCanonicalQM
abbrev M31Exact := AspisV8R15.ExactTowerBase.M31Exact
abbrev QM31Exact := AspisV8R15.ExactTowerBase.QM31Exact

def decode (x : CurrentQM) : QM31Exact :=
  ⟨⟨(x.c0.a.val : M31Exact), (x.c0.b.val : M31Exact)⟩,
    ⟨(x.c1.a.val : M31Exact), (x.c1.b.val : M31Exact)⟩⟩

theorem decode_eq_wordTower (x : CurrentQM) :
    decode x = AspisR1.TerminalV4QM31Tower.decode x := rfl

theorem current_qm_add_exact
    (x y : CurrentQM)
    (hx : CurrentCanonicalQM x) (hy : CurrentCanonicalQM y) :
    ∃ z : CurrentQM,
      AspisR1SelectedMaskProbe.field.QM31.add x y = .ok z ∧
      CurrentCanonicalQM z ∧ decode z = decode x + decode y := by
  obtain ⟨z, hz, hcanon, hdecode⟩ :=
    AspisR1.TerminalV4QM31Tower.current_qm_add_exact x y hx hy
  refine ⟨z, hz, hcanon, ?_⟩
  exact hdecode

theorem current_qm_mul_exact
    (x y : CurrentQM)
    (hx : CurrentCanonicalQM x) (hy : CurrentCanonicalQM y) :
    ∃ z : CurrentQM,
      AspisR1SelectedMaskProbe.field.QM31.mul x y = .ok z ∧
      CurrentCanonicalQM z ∧ decode z = decode x * decode y := by
  obtain ⟨z, hz, hcanon, hdecode⟩ :=
    AspisR1.TerminalV4QM31Tower.current_qm_mul_exact x y hx hy
  refine ⟨z, hz, hcanon, ?_⟩
  exact hdecode


theorem current_qm_sub_exact
    (x y : CurrentQM)
    (hx : CurrentCanonicalQM x) (hy : CurrentCanonicalQM y) :
    ∃ z : CurrentQM,
      AspisR1SelectedMaskProbe.field.QM31.sub x y = .ok z ∧
      CurrentCanonicalQM z ∧ decode z = decode x - decode y := by
  obtain ⟨z, hz, hcanon, hwords⟩ :=
    AspisR1.TerminalV4TowerSub.current_qm_sub_mod x y hx hy
  refine ⟨z, hz, hcanon, ?_⟩
  change AspisV8R17.QM31WordTower.decodeQ
      (AspisR1.TerminalV4QM31Mul.wordsQM z) =
    AspisV8R17.QM31WordTower.decodeQ
      (AspisR1.TerminalV4QM31Mul.wordsQM x) -
    AspisV8R17.QM31WordTower.decodeQ
      (AspisR1.TerminalV4QM31Mul.wordsQM y)
  have hword :
      AspisR1.TerminalV4QM31Mul.wordsQM z =
        AspisV8R17.GeneratedQM31Linear.qmSubWords
          (AspisR1.TerminalV4QM31Mul.wordsQM x)
          (AspisR1.TerminalV4QM31Mul.wordsQM y) := by
    simpa [AspisV8R17.GeneratedQM31Linear.qmSubWords,
      AspisV8R17.GeneratedQM31Products.subWords,
      AspisR1.TerminalV4QM31Mul.subWords,
      AspisR1.TerminalV4QM31Mul.wordsQM,
      AspisR1.TerminalV4QM31Mul.wordsCM,
      AspisR1.TerminalV4TowerAdd.wordsQM,
      AspisR1.TerminalV4TowerAdd.wordsCM] using hwords
  rw [hword]
  have hyWords :
      AspisV8R17.QM31WordResidues.CanonicalPair
          (AspisR1.TerminalV4QM31Mul.wordsQM y).1 ∧
      AspisV8R17.QM31WordResidues.CanonicalPair
          (AspisR1.TerminalV4QM31Mul.wordsQM y).2 := by
    rcases hy with ⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩
    constructor
    · change (y.c0.a.val < AspisV8R17.RawReducer.P) ∧
        (y.c0.b.val < AspisV8R17.RawReducer.P)
      exact ⟨by simpa [AspisR1.TerminalV4TowerAdd.P,
        AspisR1.TerminalV4M31AddSub.P] using ha,
        by simpa [AspisR1.TerminalV4TowerAdd.P,
        AspisR1.TerminalV4M31AddSub.P] using hb⟩
    · change (y.c1.a.val < AspisV8R17.RawReducer.P) ∧
        (y.c1.b.val < AspisV8R17.RawReducer.P)
      exact ⟨by simpa [AspisR1.TerminalV4TowerAdd.P,
        AspisR1.TerminalV4M31AddSub.P] using hc,
        by simpa [AspisR1.TerminalV4TowerAdd.P,
        AspisR1.TerminalV4M31AddSub.P] using hd⟩
  exact AspisV8R17.QM31WordTower.decode_sub _ _ hyWords

#print axioms decode_eq_wordTower
#print axioms current_qm_add_exact
#print axioms current_qm_mul_exact
#print axioms current_qm_sub_exact

end AspisR1.TerminalV4QM31Exact
