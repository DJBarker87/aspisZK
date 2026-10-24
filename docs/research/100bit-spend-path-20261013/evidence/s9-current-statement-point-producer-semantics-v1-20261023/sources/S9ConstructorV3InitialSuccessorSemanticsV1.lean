import S9ConstructorV3CarryLoopSemanticsV1
import S9ConstructorTensorFactorMapV1
import S9ConstructorV3Loop1CellCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ConstructorV3InitialSuccessorSemanticsV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ConstructorV3SuccessorCarryBodyCanonicalV1
open AspisR1S9ConstructorV3CarryBodySemanticsV1
open AspisR1S9ConstructorV3VectorMeaningV1
open AspisR1S9ConstructorV3CarryMeaningStepV1
open AspisR1S9ConstructorV3CarryLoopSemanticsV1

/-- Discharges the semantic carry and processed-suffix initialization premises
for the actual source loop, which starts at ONE with the input vector itself. -/
theorem initial_successor_loop_exact (p : Nat → ExactQM) (z out : Vector) (iter : ReverseRange)
    (hz : VectorCanonical z) (hzMeaning : Meaning z p)
    (hs : iter.iter.start.val=0) (he : iter.iter.end.val=10)
    (hloop : AspisR1S9ActualWeightsNewBoxNewV3.state_only_prefix.state_only_statement_points_loop
      iter z z AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE = .ok out) :
    VectorCanonical out ∧ Meaning out (successorPoint p) := by
  have hone : Can AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE :=
    AspisR1S9ConstructorV3Loop1CellCanonicalV1.one_canonical
  have honeDecode : decode AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE=1 :=
    AspisR1S9ConstructorTensorFactorMapV1.ctor_one_decode
  have hd : decode AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE =
      succCarry p (10-iter.iter.end.val) := by
    rw [he,honeDecode]
    rfl
  have hm : Meaning z (SuffixMeaning p iter.iter.end.val) := by
    intro i q hread
    have hi := index_success_bound z i q hread
    have hibound : i.val < 10 := by simpa using hi
    change decode q = (if i.val < iter.iter.end.val then p i.val else successorPoint p i.val)
    rw [if_pos (by omega)]
    exact hzMeaning i q hread
  exact carry_loop_success_exact p z z out iter _ hz hzMeaning hz hone hs (by omega) hd hm hloop

#print axioms initial_successor_loop_exact
end AspisR1S9ConstructorV3InitialSuccessorSemanticsV1
