import AllocationBatchConstantM10
import GSPointBatchWorkM10
import GSByteSamplerWorkM10

/-! Fixed-width point-generation and rejection-sampler constructor schedules.
Each point tariff covers fixed-domain point powers, cached reads and field
intermediates; each draw pays all sixteen retries of all sixteen limbs.
Both schedules retain the batch constructors, including failure outputs. -/
set_option autoImplicit false
namespace AspisR1.GSPointSamplerAllocationM10
open AspisWideTower AspisPool.AlgorithmicCircleDecoderV7
open GSFixedInputDecoderFamily M31RetryOutputFiber M31AcceptFiber

def pointCells : Nat := 1000000000

@[never_extract,noinline] def initialCells (_W : InitialWord WideExact) : Nat :=
  1048576*pointCells+3*1048576+1
@[never_extract,noinline] def finalCells (_V : FinalWord WideExact) : Nat :=
  262144*pointCells+3*262144+1

theorem initial_paid (W : InitialWord WideExact) : initialCells W ≤ (GSPointBatchWorkM10.initial W).2 := by
  have h := AllocationBatchM10.materialize_work
    (fun i : Fin 1048576 =>
      ((AspisWide.GSRuntimeInitialDistanceEncoderBridge.initialRuntimePoint i,
        (1+AspisWide.GSRuntimeInitialDistanceEncoderBridge.initialRuntimePoint i^2)^512*W i),1000000000000))
    (fun _ => pointCells) (fun _ => by change 1000000000 ≤ 1000000000000; omega)
  rw [AllocationBatchConstantM10.cells] at h
  exact h

theorem final_paid (V : FinalWord WideExact) : finalCells V ≤ (GSPointBatchWorkM10.final V).2 := by
  have h := AllocationBatchM10.materialize_work
    (fun i : Fin 262144 =>
      ((AspisWide.GSRuntimeFinalDistanceEncoderBridge.finalRuntimePoint i,V i),1000000000000))
    (fun _ => pointCells) (fun _ => by change 1000000000 ≤ 1000000000000; omega)
  rw [AllocationBatchConstantM10.cells] at h
  exact h

@[never_extract,noinline] def inputsCells (W : Fin 29 → InitialWord WideExact) (V : Fin 5 → FinalWord WideExact) : Nat :=
  AllocationBatchM10.cells (fun i => initialCells (W i))+
    AllocationBatchM10.cells (fun i => finalCells (V i))+4

theorem inputs_paid (W : Fin 29 → InitialWord WideExact) (V : Fin 5 → FinalWord WideExact) :
    inputsCells W V ≤ (GSPointBatchWorkM10.inputs W V).2 :=
  Nat.add_le_add_right (Nat.add_le_add
    (AllocationBatchM10.batch_work _ _ (fun i => initial_paid (W i)))
    (AllocationBatchM10.batch_work _ _ (fun i => final_paid (V i)))) 4

def pairCells : Nat := 16*16*128+16+1

@[never_extract,noinline] def sampleCells (n : Nat) : Nat := n*pairCells+3*n+1+2*n+1

theorem sample_paid (n : Nat) (coins : ActualWidePairInputTape n) :
    sampleCells n ≤ (GSByteSamplerWorkM10.sample n coins).2 := by
  have h := AllocationBatchM10.batch_work (fun i : Fin n => GSByteSamplerWorkM10.pair (coins i))
    (fun _ => pairCells) (fun _ => by change 16*16*128+16+1 ≤ 65536; omega)
  rw [AllocationBatchConstantM10.cells] at h
  exact Nat.add_le_add_right (Nat.add_le_add_right h (2*n)) 1

#print axioms initial_paid
#print axioms final_paid
#print axioms inputs_paid
#print axioms sample_paid
end AspisR1.GSPointSamplerAllocationM10
