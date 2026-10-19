import TerminalV4RevListTransitionV2
import TerminalV4PreparedMulCanonicalV1
import TerminalV4TowerAddV2

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace AspisR1.TerminalV4CompositionLoopCanonical
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev CanonicalQM := AspisR1.TerminalV4TowerAdd.CanonicalQM
abbrev PreparedFor := AspisR1.TerminalV4PreparedStateCurrent.PreparedFor
abbrev RevIter := Aeneas.Std.core.iter.adapters.rev.Rev

def listLoopCanonicalModel (linear : QM) (items : List QM) : Prop :=
  ∀ x ∈ items, CanonicalQM x

private theorem bindPairOk {A B C : Type} (a : A) (b : B)
    (f : A → B → Result C) :
    (do let (x, y) ← Result.ok (a, b); f x y) = f a b := rfl

theorem composition_parts_loop0_canonical
    (items : List QM) (prepared : Prepared) (linear acc : QM)
    (hlinear : CanonicalQM linear) (hprepared : PreparedFor prepared linear)
    (hacc : CanonicalQM acc) (hitems : listLoopCanonicalModel linear items) :
    ∃ out : QM,
      AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop0
        ⟨items.reverse⟩ prepared acc = .ok out ∧ CanonicalQM out := by
  induction items generalizing acc with
  | nil =>
      rw [AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop0.eq_def]
      simp only [Aeneas.Std.core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
        core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator,
        core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back,
        List.reverse_nil, bind_tc_ok]
      exact ⟨acc, rfl, hacc⟩
  | cons x xs ih =>
      have hx : CanonicalQM x := hitems x (by simp)
      have htail : listLoopCanonicalModel linear xs := by
        intro y hy
        exact hitems y (by simp [hy])
      obtain ⟨q, hq, hqcan⟩ :=
        AspisR1.TerminalV4PreparedMulCanonical.prepared_mul_canonical
          prepared linear acc hlinear hacc hprepared
      classical
      let acc1 : QM := Classical.choose
        (AspisR1.TerminalV4TowerAdd.current_qm_add_mod q x hqcan hx)
      have haddPack := Classical.choose_spec
        (AspisR1.TerminalV4TowerAdd.current_qm_add_mod q x hqcan hx)
      have hadd := haddPack.1
      have hacc1 := haddPack.2.1
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
        rfl
      obtain ⟨out, hrun, hout⟩ := ih acc1 hacc1 htail
      exact ⟨out, hcall.trans hrun, hout⟩

#print axioms composition_parts_loop0_canonical
end AspisR1.TerminalV4CompositionLoopCanonical
