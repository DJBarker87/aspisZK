import R1Z.ProverRwDictionaryLayoutArithmetic
import R1Z.ProverRwDictionaryLayoutSource
set_option autoImplicit false
namespace R1Z.ProverRwDictionaryLayoutTotal
open Aeneas Aeneas.Std Result ProverRwDictionaryLayoutSource
abbrev r22_checked_add_eq := ProverRwDictionaryLayoutArithmetic.add_eq
abbrev r22_checked_mul_eq := ProverRwDictionaryLayoutArithmetic.mul_eq
abbrev r22_checked_sub_eq := ProverRwDictionaryLayoutArithmetic.sub_eq

theorem r22_compact_SEMANTIC_COMPACT_VALUES_total : compact.SEMANTIC_COMPACT_VALUES = ok 426#usize := by
  have h0 : (10#usize * 28#usize : Result Usize) = ok 280#usize := by
    apply r22_checked_mul_eq; decide
  have h1 : (1#usize + 280#usize : Result Usize) = ok 281#usize := by
    apply r22_checked_add_eq; decide
  have h2 : (87#usize + 29#usize : Result Usize) = ok 116#usize := by
    apply r22_checked_add_eq; decide
  have h3 : (281#usize + 116#usize : Result Usize) = ok 397#usize := by
    apply r22_checked_add_eq; decide
  have h4 : (397#usize + 29#usize : Result Usize) = ok 426#usize := by
    apply r22_checked_add_eq; decide
  simp only [compact.SEMANTIC_COMPACT_VALUES, h0, h1, h2, h3, h4, bind_tc_ok]

theorem r22_verifier_SEMANTIC_BYTES_total : verifier.SEMANTIC_BYTES = ok 13831#usize := by
  have h0 : (29#usize * 32#usize : Result Usize) = ok 928#usize := by
    apply r22_checked_mul_eq; decide
  have h1 : (12903#usize + 928#usize : Result Usize) = ok 13831#usize := by
    apply r22_checked_add_eq; decide
  simp only [verifier.SEMANTIC_BYTES, h0, h1, bind_tc_ok]

theorem r22_compact_LOGICAL_SEMANTIC_total : compact.LOGICAL_SEMANTIC = ok 13831#usize := by

  simp only [compact.LOGICAL_SEMANTIC, r22_verifier_SEMANTIC_BYTES_total, bind_tc_ok]

theorem r22_compact_COMPACT_SEMANTIC_total : compact.COMPACT_SEMANTIC = ok 7015#usize := by
  have h0 : (16#usize * 426#usize : Result Usize) = ok 6816#usize := by
    apply r22_checked_mul_eq; decide
  have h1 : (13831#usize - 6816#usize : Result Usize) = ok 7015#usize := by
    apply r22_checked_sub_eq <;> decide
  simp only [compact.COMPACT_SEMANTIC, r22_compact_SEMANTIC_COMPACT_VALUES_total, r22_compact_LOGICAL_SEMANTIC_total, h0, h1, bind_tc_ok]

theorem r22_compact_OFF_Y1_total : compact.OFF_Y1 = ok 7031#usize := by
  have h0 : (16#usize + 7015#usize : Result Usize) = ok 7031#usize := by
    apply r22_checked_add_eq; decide
  simp only [compact.OFF_Y1, r22_compact_COMPACT_SEMANTIC_total, compact.OFF_SEMANTIC, compact.HEADER, h0, bind_tc_ok]

theorem r22_compact_COMPACT_Y1_total : compact.COMPACT_Y1 = ok 464#usize := by
  have h0 : (29#usize * 16#usize : Result Usize) = ok 464#usize := by
    apply r22_checked_mul_eq; decide
  simp only [compact.COMPACT_Y1, h0, bind_tc_ok]

theorem r22_compact_OFF_INACTIVE_total : compact.OFF_INACTIVE = ok 7495#usize := by
  have h0 : (7031#usize + 464#usize : Result Usize) = ok 7495#usize := by
    apply r22_checked_add_eq; decide
  simp only [compact.OFF_INACTIVE, r22_compact_OFF_Y1_total, r22_compact_COMPACT_Y1_total, h0, bind_tc_ok]

theorem r22_compact_OFF_ROUND0_total : compact.OFF_ROUND0 = ok 7527#usize := by
  have h0 : (7495#usize + 32#usize : Result Usize) = ok 7527#usize := by
    apply r22_checked_add_eq; decide
  simp only [compact.OFF_ROUND0, r22_compact_OFF_INACTIVE_total, h0, bind_tc_ok]

theorem r22_compact_OFF_FOLDED_ROOT_total : compact.OFF_FOLDED_ROOT = ok 7751#usize := by
  have h0 : (7527#usize + 224#usize : Result Usize) = ok 7751#usize := by
    apply r22_checked_add_eq; decide
  simp only [compact.OFF_FOLDED_ROOT, r22_compact_OFF_ROUND0_total, h0, bind_tc_ok]

theorem r22_compact_OFF_ROUND1_total : compact.OFF_ROUND1 = ok 7783#usize := by
  have h0 : (7751#usize + 32#usize : Result Usize) = ok 7783#usize := by
    apply r22_checked_add_eq; decide
  simp only [compact.OFF_ROUND1, r22_compact_OFF_FOLDED_ROOT_total, h0, bind_tc_ok]

theorem r22_compact_OFF_FINAL_total : compact.OFF_FINAL = ok 8007#usize := by
  have h0 : (7783#usize + 224#usize : Result Usize) = ok 8007#usize := by
    apply r22_checked_add_eq; decide
  simp only [compact.OFF_FINAL, r22_compact_OFF_ROUND1_total, h0, bind_tc_ok]

theorem r22_compact_OFF_OPENINGS_total : compact.OFF_OPENINGS = ok 10055#usize := by
  have h0 : (64#usize * 32#usize : Result Usize) = ok 2048#usize := by
    apply r22_checked_mul_eq; decide
  have h1 : (8007#usize + 2048#usize : Result Usize) = ok 10055#usize := by
    apply r22_checked_add_eq; decide
  simp only [compact.OFF_OPENINGS, r22_compact_OFF_FINAL_total, compact.FINAL_LEN, h0, h1, bind_tc_ok]

theorem r22_compact_OPENING_total : compact.OPENING = ok 832#usize := by
  have h0 : (480#usize + 128#usize : Result Usize) = ok 608#usize := by
    apply r22_checked_add_eq; decide
  have h1 : (608#usize + 32#usize : Result Usize) = ok 640#usize := by
    apply r22_checked_add_eq; decide
  have h2 : (640#usize + 32#usize : Result Usize) = ok 672#usize := by
    apply r22_checked_add_eq; decide
  have h3 : (672#usize + 128#usize : Result Usize) = ok 800#usize := by
    apply r22_checked_add_eq; decide
  have h4 : (800#usize + 32#usize : Result Usize) = ok 832#usize := by
    apply r22_checked_add_eq; decide
  simp only [compact.OPENING, h0, h1, h2, h3, h4, bind_tc_ok]

theorem r22_compact_OFF_NODES_total : compact.OFF_NODES = ok 28359#usize := by
  have h0 : (22#usize * 832#usize : Result Usize) = ok 18304#usize := by
    apply r22_checked_mul_eq; decide
  have h1 : (10055#usize + 18304#usize : Result Usize) = ok 28359#usize := by
    apply r22_checked_add_eq; decide
  simp only [compact.OFF_NODES, r22_compact_OFF_OPENINGS_total, r22_compact_OPENING_total, compact.QUERIES, h0, h1, bind_tc_ok]

theorem r22_compact_MAX_NODES_total : compact.MAX_NODES = ok 914#usize := by
  have h0 : (146#usize + 172#usize : Result Usize) = ok 318#usize := by
    apply r22_checked_add_eq; decide
  have h1 : (2#usize * 318#usize : Result Usize) = ok 636#usize := by
    apply r22_checked_mul_eq; decide
  have h2 : (128#usize + 150#usize : Result Usize) = ok 278#usize := by
    apply r22_checked_add_eq; decide
  have h3 : (636#usize + 278#usize : Result Usize) = ok 914#usize := by
    apply r22_checked_add_eq; decide
  simp only [compact.MAX_NODES, h0, h1, h2, h3, bind_tc_ok]

theorem r22_compact_FIXED_total : compact.FIXED = ok 28359#usize := by

  simp only [compact.FIXED, r22_compact_OFF_NODES_total, bind_tc_ok]

theorem r22_compact_MAX_PROOF_total : compact.MAX_PROOF = ok 57607#usize := by
  have h0 : (32#usize * 914#usize : Result Usize) = ok 29248#usize := by
    apply r22_checked_mul_eq; decide
  have h1 : (28359#usize + 29248#usize : Result Usize) = ok 57607#usize := by
    apply r22_checked_add_eq; decide
  simp only [compact.MAX_PROOF, r22_compact_MAX_NODES_total, r22_compact_FIXED_total, h0, h1, bind_tc_ok]

theorem r22_compact_PROOF_BYTES_total : compact.PROOF_BYTES = ok 57607#usize := by

  simp only [compact.PROOF_BYTES, r22_compact_MAX_PROOF_total, bind_tc_ok]

#print axioms r22_compact_SEMANTIC_COMPACT_VALUES_total
#print axioms r22_verifier_SEMANTIC_BYTES_total
#print axioms r22_compact_LOGICAL_SEMANTIC_total
#print axioms r22_compact_COMPACT_SEMANTIC_total
#print axioms r22_compact_OFF_Y1_total
#print axioms r22_compact_COMPACT_Y1_total
#print axioms r22_compact_OFF_INACTIVE_total
#print axioms r22_compact_OFF_ROUND0_total
#print axioms r22_compact_OFF_FOLDED_ROOT_total
#print axioms r22_compact_OFF_ROUND1_total
#print axioms r22_compact_OFF_FINAL_total
#print axioms r22_compact_OFF_OPENINGS_total
#print axioms r22_compact_OPENING_total
#print axioms r22_compact_OFF_NODES_total
#print axioms r22_compact_MAX_NODES_total
#print axioms r22_compact_FIXED_total
#print axioms r22_compact_MAX_PROOF_total
#print axioms r22_compact_PROOF_BYTES_total
end R1Z.ProverRwDictionaryLayoutTotal
