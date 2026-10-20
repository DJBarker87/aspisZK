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
abbrev decode := AspisR1.TerminalV4EqualityValueAdapter.decode
abbrev factorAt := AspisR1.TerminalV4EqualityValueLoop.factorAt

theorem actual_result_canonical_and_value (left right : Arr) (q : QM)
    (hleft : ∀ i : Fin 10,
      Canonical (left.val[i.val]'(by simpa [left.property] using i.isLt)))
    (hright : ∀ i : Fin 10,
      Canonical (right.val[i.val]'(by simpa [right.property] using i.isLt)))
    (hresult : pool_v1.pair_forest_semantic_terminal.equality_value left right = .ok q) :
    Canonical q ∧
      decode q = factorAt left right ⟨0, by omega⟩ *
        (∏ i : Fin 9, factorAt left right i.succ) := by
  obtain ⟨out, hout, hcanonical, hvalue⟩ :=
    AspisR1.TerminalV4EqualityValueLoop.equality_value_success left right hleft hright
  have heq : out = q := Result.ok.inj (hout.symm.trans hresult)
  subst q
  exact ⟨hcanonical, hvalue⟩

#print axioms AspisR1.TerminalV4EqualityValueResultRefinement.actual_result_canonical_and_value
end AspisR1.TerminalV4EqualityValueResultRefinement
