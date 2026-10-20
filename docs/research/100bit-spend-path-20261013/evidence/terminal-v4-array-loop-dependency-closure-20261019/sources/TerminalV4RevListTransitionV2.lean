import TerminalV4CompositionLoopsChunk06V5
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace AspisR1.TerminalV4RevListTransitionV2
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31

theorem reverse_next_empty {N : Usize} (xs : List QM) (h : xs = []) :
    Aeneas.Std.core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator QM N)
      ⟨xs⟩ = .ok (none, ⟨xs⟩) := by
  subst xs
  simp [Aeneas.Std.core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator,
    core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back]

theorem reverse_next_append {N : Usize} (ys : List QM) (x : QM) :
    Aeneas.Std.core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator QM N)
      ⟨ys ++ [x]⟩ = .ok (some x, ⟨ys⟩) := by
  simp [Aeneas.Std.core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator,
    core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back,
    List.reverse_append, List.reverse_reverse]
end AspisR1.TerminalV4RevListTransitionV2
#print axioms AspisR1.TerminalV4RevListTransitionV2.reverse_next_empty
#print axioms AspisR1.TerminalV4RevListTransitionV2.reverse_next_append
