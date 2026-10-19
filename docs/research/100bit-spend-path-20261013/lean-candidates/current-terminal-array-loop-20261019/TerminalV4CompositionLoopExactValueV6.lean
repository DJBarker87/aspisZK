import TerminalV4CompositionLoopCanonicalV12
import TerminalV4PreparedMulExactCurrent
import TerminalV4QM31TowerCurrent
import AspisV8R15.ExactTowerBase

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace AspisR1.TerminalV4CompositionLoopExactValue
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev CanonicalQM := AspisR1.TerminalV4TowerAdd.CanonicalQM
abbrev PreparedFor := AspisR1.TerminalV4PreparedStateCurrent.PreparedFor
abbrev ExactQM := AspisV8R17.QM31WordTower.Q
abbrev decode := AspisR1.TerminalV4QM31TowerCurrent.decode

def listHorner (linear : ExactQM) : List QM → ExactQM → ExactQM
  | [], acc => acc
  | x :: xs, acc => listHorner linear xs (linear * acc + decode x)

private theorem bindPairOk {A B C : Type} (a : A) (b : B)
    (f : A → B → Result C) :
    (do let (x, y) ← Result.ok (a, b); f x y) = f a b := rfl

theorem composition_parts_loop0_exact_value
    (items : List QM) (prepared : Prepared) (linear acc : QM)
    (hlinear : CanonicalQM linear) (hprepared : PreparedFor prepared linear)
    (hacc : CanonicalQM acc)
    (hitems : AspisR1.TerminalV4CompositionLoopCanonical.listLoopCanonicalModel linear items) :
    ∃ out : QM,
      AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop0
        ⟨items.reverse⟩ prepared acc = .ok out ∧
      CanonicalQM out ∧
      decode out = listHorner (decode linear) items (decode acc) := by
  induction items generalizing acc with
  | nil =>
      refine ⟨acc, ?_, hacc, rfl⟩
      rw [AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop0.eq_def]
      simp only [Aeneas.Std.core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
        core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator,
        core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back,
        List.reverse_nil, bind_tc_ok]
      rfl
  | cons x xs ih =>
      have hx : CanonicalQM x := hitems x (by simp)
      have htail : AspisR1.TerminalV4CompositionLoopCanonical.listLoopCanonicalModel linear xs := by
        intro y hy
        exact hitems y (by simp [hy])
      obtain ⟨q, hq, hqcan, hqvalue⟩ :=
        AspisR1.TerminalV4PreparedMulExactCurrent.prepared_mul_exact prepared linear acc
          hlinear hacc hprepared
      obtain ⟨acc1, hadd, hacc1, haddValue⟩ :=
        AspisR1.TerminalV4QM31TowerCurrent.current_qm_add_exact q x hqcan hx
      have hcall :
          AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop0
            ⟨(x :: xs).reverse⟩ prepared acc =
          AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop0
            ⟨xs.reverse⟩ prepared acc1 := by
        rw [List.reverse_cons]
        rw [AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop0.eq_def]
        rw [AspisR1.TerminalV4RevListTransitionV2.reverse_next_append]
        rw [bindPairOk]
        rw [hq]
        simp only [bind_tc_ok]
        rw [hadd]
        simp only [bind_tc_ok]
      obtain ⟨out, hrun, hout, hvalue⟩ := ih acc1 hacc1 htail
      refine ⟨out, hcall.trans hrun, hout, ?_⟩
      simp only [listHorner]
      rw [hvalue]
      apply congrArg (listHorner (decode linear) xs)
      calc
        decode acc1 = decode q + decode x := haddValue
        _ = decode linear * decode acc + decode x := by
          change AspisR1.TerminalV4QM31TowerCurrent.decode q +
              AspisR1.TerminalV4QM31TowerCurrent.decode x =
            AspisR1.TerminalV4QM31TowerCurrent.decode linear *
              AspisR1.TerminalV4QM31TowerCurrent.decode acc +
              AspisR1.TerminalV4QM31TowerCurrent.decode x
          rw [hqvalue]

#print axioms composition_parts_loop0_exact_value
end AspisR1.TerminalV4CompositionLoopExactValue
