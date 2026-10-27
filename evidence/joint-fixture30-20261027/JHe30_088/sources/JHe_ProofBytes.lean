import AdapterRwScalar
set_option autoImplicit false
namespace AspisR1.JHe_ProofBytes
open Aeneas Aeneas.Std Result
open _root_.AdapterRw aspis_r1_cost_probe AspisR1.AdapterRw.Scalar
theorem proof_bytes : compact.PROOF_BYTES = ok 57607#usize := by
  simp only [verifier.SEMANTIC_BYTES, compact.MAX_NODES, compact.FINAL_LEN, compact.HEADER, compact.OFF_SEMANTIC, compact.SEMANTIC_COMPACT_VALUES, compact.LOGICAL_SEMANTIC, compact.COMPACT_SEMANTIC, compact.OFF_Y1, compact.COMPACT_Y1, compact.OFF_INACTIVE, compact.OFF_ROUND0, compact.OFF_FOLDED_ROOT, compact.OFF_ROUND1, compact.OFF_FINAL, compact.OFF_OPENINGS, compact.OPENING, compact.QUERIES, compact.OFF_NODES, compact.FIXED, compact.MAX_PROOF, compact.PROOF_BYTES]
  simp only [
    add_eq 146#usize 172#usize 318#usize (by scalar_tac),
    mul_eq 2#usize 318#usize 636#usize (by scalar_tac),
    add_eq 128#usize 150#usize 278#usize (by scalar_tac),
    add_eq 636#usize 278#usize 914#usize (by scalar_tac),
    mul_eq 32#usize 914#usize 29248#usize (by scalar_tac),
    add_eq 480#usize 128#usize 608#usize (by scalar_tac),
    add_eq 608#usize 32#usize 640#usize (by scalar_tac),
    add_eq 640#usize 32#usize 672#usize (by scalar_tac),
    add_eq 672#usize 128#usize 800#usize (by scalar_tac),
    add_eq 800#usize 32#usize 832#usize (by scalar_tac),
    mul_eq 22#usize 832#usize 18304#usize (by scalar_tac),
    mul_eq 64#usize 32#usize 2048#usize (by scalar_tac),
    mul_eq 10#usize 28#usize 280#usize (by scalar_tac),
    add_eq 1#usize 280#usize 281#usize (by scalar_tac),
    add_eq 87#usize 29#usize 116#usize (by scalar_tac),
    add_eq 281#usize 116#usize 397#usize (by scalar_tac),
    add_eq 397#usize 29#usize 426#usize (by scalar_tac),
    mul_eq 16#usize 426#usize 6816#usize (by scalar_tac),
    mul_eq 29#usize 32#usize 928#usize (by scalar_tac),
    add_eq 12903#usize 928#usize 13831#usize (by scalar_tac),
    sub_eq 13831#usize 6816#usize 7015#usize (by scalar_tac) (by scalar_tac),
    add_eq 16#usize 7015#usize 7031#usize (by scalar_tac),
    mul_eq 29#usize 16#usize 464#usize (by scalar_tac),
    add_eq 7031#usize 464#usize 7495#usize (by scalar_tac),
    add_eq 7495#usize 32#usize 7527#usize (by scalar_tac),
    add_eq 7527#usize 224#usize 7751#usize (by scalar_tac),
    add_eq 7751#usize 32#usize 7783#usize (by scalar_tac),
    add_eq 7783#usize 224#usize 8007#usize (by scalar_tac),
    add_eq 8007#usize 2048#usize 10055#usize (by scalar_tac),
    add_eq 10055#usize 18304#usize 28359#usize (by scalar_tac),
    add_eq 28359#usize 29248#usize 57607#usize (by scalar_tac),
    bind_tc_ok]

#print axioms proof_bytes
end AspisR1.JHe_ProofBytes
