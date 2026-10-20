import Aeneas
import QueryValidatorGeneratedPrefix
import QueryValidatorChunkNoHit
import QueryValidatorChunks12NoHit
import QueryValidatorLoopInvariant
import Aeneas.Tactic.Solver.ScalarTac
open Aeneas Aeneas.Std Result AspisR1Stage2AdoptedResume
namespace AspisR1.QueryValidatorChunkNoHitValues
abbrev QueryArray := Array Std.U32 22#usize
open AspisR1.QueryValidatorChunkNoHit
open AspisR1.QueryValidatorChunks12NoHit
open AspisR1.QueryValidatorLoopInvariant

theorem chunk0_values_nohit
    (queries : QueryArray) (needle : Std.U32) (count : Usize)
    (hfalse : verifier.query_duplicate_chunk0 queries needle count = ok false) :
    ∀ j : Nat, j < 8 → j < count.val → queryValue queries (j + 0) ≠ needle.val := by
  have hno := chunk0_nohit queries needle count hfalse
  intro j hjblock hjcount
  have hjcase : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases hjcase with hj0 | hj1 | hj2 | hj3 | hj4 | hj5 | hj6 | hj7
  ·
    subst j
    have hc : (count > 0#usize) = true := by scalar_tac
    have hneq := hno.1 hc
    intro heq
    apply hneq
    apply UScalar.val_eq_imp
    simpa [queryValue] using heq
  ·
    subst j
    have hc : (count > 1#usize) = true := by scalar_tac
    have hneq := hno.2.1 hc
    intro heq
    apply hneq
    apply UScalar.val_eq_imp
    simpa [queryValue] using heq
  ·
    subst j
    have hc : (count > 2#usize) = true := by scalar_tac
    have hneq := hno.2.2.1 hc
    intro heq
    apply hneq
    apply UScalar.val_eq_imp
    simpa [queryValue] using heq
  ·
    subst j
    have hc : (count > 3#usize) = true := by scalar_tac
    have hneq := hno.2.2.2.1 hc
    intro heq
    apply hneq
    apply UScalar.val_eq_imp
    simpa [queryValue] using heq
  ·
    subst j
    have hc : (count > 4#usize) = true := by scalar_tac
    have hneq := hno.2.2.2.2.1 hc
    intro heq
    apply hneq
    apply UScalar.val_eq_imp
    simpa [queryValue] using heq
  ·
    subst j
    have hc : (count > 5#usize) = true := by scalar_tac
    have hneq := hno.2.2.2.2.2.1 hc
    intro heq
    apply hneq
    apply UScalar.val_eq_imp
    simpa [queryValue] using heq
  ·
    subst j
    have hc : (count > 6#usize) = true := by scalar_tac
    have hneq := hno.2.2.2.2.2.2.1 hc
    intro heq
    apply hneq
    apply UScalar.val_eq_imp
    simpa [queryValue] using heq
  ·
    subst j
    have hc : (count > 7#usize) = true := by scalar_tac
    have hneq := hno.2.2.2.2.2.2.2 hc
    intro heq
    apply hneq
    apply UScalar.val_eq_imp
    simpa [queryValue] using heq

#print axioms chunk0_values_nohit

theorem chunk1_values_nohit
    (queries : QueryArray) (needle : Std.U32) (count : Usize)
    (hfalse : verifier.query_duplicate_chunk1 queries needle count = ok false) :
    ∀ j : Nat, j < 8 → j < count.val → queryValue queries (j + 8) ≠ needle.val := by
  have hno := chunk1_nohit queries needle count hfalse
  intro j hjblock hjcount
  have hjcase : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases hjcase with hj0 | hj1 | hj2 | hj3 | hj4 | hj5 | hj6 | hj7
  ·
    subst j
    have hc : (count > 0#usize) = true := by scalar_tac
    have hneq := hno.1 hc
    intro heq
    apply hneq
    apply UScalar.val_eq_imp
    simpa [queryValue] using heq
  ·
    subst j
    have hc : (count > 1#usize) = true := by scalar_tac
    have hneq := hno.2.1 hc
    intro heq
    apply hneq
    apply UScalar.val_eq_imp
    simpa [queryValue] using heq
  ·
    subst j
    have hc : (count > 2#usize) = true := by scalar_tac
    have hneq := hno.2.2.1 hc
    intro heq
    apply hneq
    apply UScalar.val_eq_imp
    simpa [queryValue] using heq
  ·
    subst j
    have hc : (count > 3#usize) = true := by scalar_tac
    have hneq := hno.2.2.2.1 hc
    intro heq
    apply hneq
    apply UScalar.val_eq_imp
    simpa [queryValue] using heq
  ·
    subst j
    have hc : (count > 4#usize) = true := by scalar_tac
    have hneq := hno.2.2.2.2.1 hc
    intro heq
    apply hneq
    apply UScalar.val_eq_imp
    simpa [queryValue] using heq
  ·
    subst j
    have hc : (count > 5#usize) = true := by scalar_tac
    have hneq := hno.2.2.2.2.2.1 hc
    intro heq
    apply hneq
    apply UScalar.val_eq_imp
    simpa [queryValue] using heq
  ·
    subst j
    have hc : (count > 6#usize) = true := by scalar_tac
    have hneq := hno.2.2.2.2.2.2.1 hc
    intro heq
    apply hneq
    apply UScalar.val_eq_imp
    simpa [queryValue] using heq
  ·
    subst j
    have hc : (count > 7#usize) = true := by scalar_tac
    have hneq := hno.2.2.2.2.2.2.2 hc
    intro heq
    apply hneq
    apply UScalar.val_eq_imp
    simpa [queryValue] using heq

#print axioms chunk1_values_nohit

theorem chunk2_values_nohit
    (queries : QueryArray) (needle : Std.U32) (count : Usize)
    (hfalse : verifier.query_duplicate_chunk2 queries needle count = ok false) :
    ∀ j : Nat, j < 6 → j < count.val → queryValue queries (j + 16) ≠ needle.val := by
  have hno := chunk2_nohit queries needle count hfalse
  intro j hjblock hjcount
  have hjcase : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases hjcase with hj0 | hj1 | hj2 | hj3 | hj4 | hj5
  ·
    subst j
    have hc : (count > 0#usize) = true := by scalar_tac
    have hneq := hno.1 hc
    intro heq
    apply hneq
    apply UScalar.val_eq_imp
    simpa [queryValue] using heq
  ·
    subst j
    have hc : (count > 1#usize) = true := by scalar_tac
    have hneq := hno.2.1 hc
    intro heq
    apply hneq
    apply UScalar.val_eq_imp
    simpa [queryValue] using heq
  ·
    subst j
    have hc : (count > 2#usize) = true := by scalar_tac
    have hneq := hno.2.2.1 hc
    intro heq
    apply hneq
    apply UScalar.val_eq_imp
    simpa [queryValue] using heq
  ·
    subst j
    have hc : (count > 3#usize) = true := by scalar_tac
    have hneq := hno.2.2.2.1 hc
    intro heq
    apply hneq
    apply UScalar.val_eq_imp
    simpa [queryValue] using heq
  ·
    subst j
    have hc : (count > 4#usize) = true := by scalar_tac
    have hneq := hno.2.2.2.2.1 hc
    intro heq
    apply hneq
    apply UScalar.val_eq_imp
    simpa [queryValue] using heq
  ·
    subst j
    have hc : (count > 5#usize) = true := by scalar_tac
    have hneq := hno.2.2.2.2.2 hc
    intro heq
    apply hneq
    apply UScalar.val_eq_imp
    simpa [queryValue] using heq

#print axioms chunk2_values_nohit

end AspisR1.QueryValidatorChunkNoHitValues
