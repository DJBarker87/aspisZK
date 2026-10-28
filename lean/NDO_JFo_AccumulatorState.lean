import RPt_JFo_Prepared
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFo_AccumulatorState
open Aeneas Aeneas.Std Result AspisR1Stage2
open OraclePortCheckpointAbiC5 CheckpointBytes4ReaderFields CheckpointBytes5Output

theorem source (a : verifier.Accumulator) (weights : Fin 64 → K) (rhs : E) (power : K)
    (contents : a.weights.val=(List.ofFn weights).map sourceK)
    (hr : sourceE rhs=a.rhs) (hp : sourceK power=a.power) (hn : a.next.val=10) :
    accumulator a=(⟨weights,rhs,power,10⟩ : QueryAccumulator.State K E) := by
  unfold accumulator
  congr 1
  · funext j
    change ofK ((a.weights.val[j.val]?).getD (sourceK 0))=weights j
    rw [contents]
    simp only [List.getElem?_map,List.getElem?_ofFn,j.isLt,↓reduceDIte,
      Option.map_some,Option.getD_some,ofK_source]
  · change ofE a.rhs=rhs
    rw [←hr,ofE_source]
  · change ofK a.power=power
    rw [←hp,ofK_source]

#print axioms source
end AspisR1.JFo_AccumulatorState
end
