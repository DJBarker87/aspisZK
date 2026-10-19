import TerminalV4EqualityValueLoopV9

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AspisR1.TerminalV4EqualityValueResultRefinement
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.TerminalV4EqualityValueLoop

abbrev QM := AspisR1.TerminalV4EqualityValueLoop.QM
abbrev Arr := AspisR1.TerminalV4EqualityValueLoop.Arr
abbrev ExactQM := AspisR1.TerminalV4EqualityValueLoop.ExactQM
abbrev Canonical := AspisR1.TerminalV4EqualityValueLoop.Canonical

@[irreducible] def expectedEquality (left right : Arr) : ExactQM :=
  AspisR1.TerminalV4EqualityValueLoop.factorAt left right ⟨0, by omega⟩ *
    AspisR1.TerminalV4EqualityValueLoop.suffixProduct left right 1

@[irreducible] def HasExpectedEquality (left right : Arr) (q : QM) : Prop :=
  AspisR1.TerminalV4EqualityValueAdapter.decode q = expectedEquality left right

theorem equality_value_exists_canonical_and_exact (left right : Arr)
    (hleft : ∀ i : Fin 10,
      Canonical (left.val[i.val]'(by simpa [left.property] using i.isLt)))
    (hright : ∀ i : Fin 10,
      Canonical (right.val[i.val]'(by simpa [right.property] using i.isLt))) :
    ∃ q : QM, pool_v1.pair_forest_semantic_terminal.equality_value left right = .ok q ∧
      Canonical q ∧ HasExpectedEquality left right q := by
  obtain ⟨out, hout, hcanonical, hvalue⟩ :=
    AspisR1.TerminalV4EqualityValueLoop.equality_value_success left right hleft hright
  refine ⟨out, hout, hcanonical, ?_⟩
  unfold HasExpectedEquality expectedEquality
  rw [AspisR1.TerminalV4EqualityValueLoop.suffixProduct_one_eq_fin9]
  exact hvalue

theorem actual_result_canonical (left right : Arr) (q : QM)
    (hleft : ∀ i : Fin 10,
      Canonical (left.val[i.val]'(by simpa [left.property] using i.isLt)))
    (hright : ∀ i : Fin 10,
      Canonical (right.val[i.val]'(by simpa [right.property] using i.isLt)))
    (hresult : pool_v1.pair_forest_semantic_terminal.equality_value left right = .ok q) :
    Canonical q := by
  obtain ⟨out, hout, hcanonical, _hvalue⟩ :=
    AspisR1.TerminalV4EqualityValueLoop.equality_value_success left right hleft hright
  have heq : out = q := Result.ok.inj (hout.symm.trans hresult)
  subst q
  exact hcanonical

#print axioms AspisR1.TerminalV4EqualityValueResultRefinement.equality_value_exists_canonical_and_exact
#print axioms AspisR1.TerminalV4EqualityValueResultRefinement.actual_result_canonical
end AspisR1.TerminalV4EqualityValueResultRefinement
