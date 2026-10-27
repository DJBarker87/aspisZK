import PSem_SourceCuts
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.PAln_Offsets
open AspisR1SelectedWideViewV1

theorem offsets :
    compact.OFF_INACTIVE=ok 7495#usize ∧ compact.OFF_ROUND0=ok 7527#usize ∧
    compact.OFF_FOLDED_ROOT=ok 7751#usize ∧ compact.OFF_ROUND1=ok 7783#usize ∧
    compact.OFF_FINAL=ok 8007#usize ∧ compact.OFF_OPENINGS=ok 10055#usize := by
  simp only [compact.OFF_INACTIVE,compact.OFF_Y1,compact.OFF_SEMANTIC,compact.HEADER,
    compact.COMPACT_SEMANTIC,compact.SEMANTIC_COMPACT_VALUES,compact.LOGICAL_SEMANTIC,
    verifier.SEMANTIC_BYTES,compact.COMPACT_Y1,compact.OFF_ROUND0,compact.OFF_FOLDED_ROOT,
    compact.OFF_ROUND1,compact.OFF_FINAL,compact.OFF_OPENINGS,compact.FINAL_LEN]
  scalar_tac

#print axioms offsets
end AspisR1.PAln_Offsets
