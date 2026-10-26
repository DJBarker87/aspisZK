import AbstractStageSpecM10
import GSPointBatchWorkM10

set_option autoImplicit false
namespace AspisR1.PointStageSpecM10
open AspisWideTower AspisPool.AlgorithmicCircleDecoderV7 GSFixedInputDecoderFamily
open AbstractStageSpecM10

attribute [local irreducible] GSPointBatchWorkM10.inputs GSPointBatchWorkM10.budget
  AspisWide.GSConcreteReceivedWordInputs.fromWords

abbrev WordPair := (Fin 29 → InitialWord WideExact) × (Fin 5 → FinalWord WideExact)

@[irreducible] def spec : StageSpec
    (fun w : WordPair => some (AspisWide.GSConcreteReceivedWordInputs.fromWords w.1 w.2))
    (fun _ => True) (fun _ => True) (fun _ => GSPointBatchWorkM10.budget) :=
  @pureStage WordPair (Inputs WideExact 5) (fun w => AspisWide.GSConcreteReceivedWordInputs.fromWords w.1 w.2)
    (fun w => GSPointBatchWorkM10.inputs w.1 w.2) _
    (fun w => GSPointBatchWorkM10.inputs_value w.1 w.2)
    (fun _ w => GSPointBatchWorkM10.inputs_work w.1 w.2)

theorem value (w : WordPair) : (spec.run w).1 =
    some (AspisWide.GSConcreteReceivedWordInputs.fromWords w.1 w.2) := spec.value w

theorem work (L : Nat) (w : WordPair) : (spec.run w).2 ≤ GSPointBatchWorkM10.budget :=
  spec.work L w True.intro

#print axioms value
#print axioms work
end AspisR1.PointStageSpecM10
