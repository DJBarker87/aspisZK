import RPz7_PSem_SourceCuts
import RPz7_PAln_Arithmetic
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.PAln_Offsets
open AspisR1SelectedWideViewV1

theorem offsets :
    compact.OFF_INACTIVE=ok 7495#usize ∧ compact.OFF_ROUND0=ok 7527#usize ∧
    compact.OFF_FOLDED_ROOT=ok 7751#usize ∧ compact.OFF_ROUND1=ok 7783#usize ∧
    compact.OFF_FINAL=ok 8007#usize ∧ compact.OFF_OPENINGS=ok 10055#usize := by
  have h0 : (10#usize*28#usize : Result Usize)=ok 280#usize :=
    PAln_Arithmetic.mul _ _ _ (by scalar_tac)
  have h1 : (1#usize+280#usize : Result Usize)=ok 281#usize :=
    PAln_Arithmetic.add _ _ _ (by scalar_tac)
  have h2 : (87#usize+29#usize : Result Usize)=ok 116#usize :=
    PAln_Arithmetic.add _ _ _ (by scalar_tac)
  have h3 : (281#usize+116#usize : Result Usize)=ok 397#usize :=
    PAln_Arithmetic.add _ _ _ (by scalar_tac)
  have h4 : (397#usize+29#usize : Result Usize)=ok 426#usize :=
    PAln_Arithmetic.add _ _ _ (by scalar_tac)
  have h5 : (16#usize*426#usize : Result Usize)=ok 6816#usize :=
    PAln_Arithmetic.mul _ _ _ (by scalar_tac)
  have h6 : (29#usize*32#usize : Result Usize)=ok 928#usize :=
    PAln_Arithmetic.mul _ _ _ (by scalar_tac)
  have h7 : (12903#usize+928#usize : Result Usize)=ok 13831#usize :=
    PAln_Arithmetic.add _ _ _ (by scalar_tac)
  have h8 : (13831#usize-6816#usize : Result Usize)=ok 7015#usize :=
    PAln_Arithmetic.sub _ _ _ (by scalar_tac) (by scalar_tac)
  have h9 : (16#usize+7015#usize : Result Usize)=ok 7031#usize :=
    PAln_Arithmetic.add _ _ _ (by scalar_tac)
  have h10 : (29#usize*16#usize : Result Usize)=ok 464#usize :=
    PAln_Arithmetic.mul _ _ _ (by scalar_tac)
  have h11 : (7031#usize+464#usize : Result Usize)=ok 7495#usize :=
    PAln_Arithmetic.add _ _ _ (by scalar_tac)
  have h12 : (7495#usize+32#usize : Result Usize)=ok 7527#usize :=
    PAln_Arithmetic.add _ _ _ (by scalar_tac)
  have h13 : (7527#usize+224#usize : Result Usize)=ok 7751#usize :=
    PAln_Arithmetic.add _ _ _ (by scalar_tac)
  have h14 : (7751#usize+32#usize : Result Usize)=ok 7783#usize :=
    PAln_Arithmetic.add _ _ _ (by scalar_tac)
  have h15 : (7783#usize+224#usize : Result Usize)=ok 8007#usize :=
    PAln_Arithmetic.add _ _ _ (by scalar_tac)
  have h16 : (64#usize*32#usize : Result Usize)=ok 2048#usize :=
    PAln_Arithmetic.mul _ _ _ (by scalar_tac)
  have h17 : (8007#usize+2048#usize : Result Usize)=ok 10055#usize :=
    PAln_Arithmetic.add _ _ _ (by scalar_tac)
  simp only [compact.OFF_INACTIVE,compact.OFF_Y1,compact.OFF_SEMANTIC,compact.HEADER,
    compact.COMPACT_SEMANTIC,compact.SEMANTIC_COMPACT_VALUES,compact.LOGICAL_SEMANTIC,
    verifier.SEMANTIC_BYTES,compact.COMPACT_Y1,compact.OFF_ROUND0,compact.OFF_FOLDED_ROOT,
    compact.OFF_ROUND1,compact.OFF_FINAL,compact.OFF_OPENINGS,compact.FINAL_LEN,
    h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,bind_tc_ok]
  simp

#print axioms offsets
end AspisR1.PAln_Offsets
