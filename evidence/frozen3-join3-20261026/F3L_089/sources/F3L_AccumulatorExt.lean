import OraclePortCheckpointAbiC5
set_option autoImplicit false
namespace AspisR1.F3L_AccumulatorExt

theorem fields (p q : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
    (weights : p.weights=q.weights) (rhs : p.rhs=q.rhs) (power : p.power=q.power) (next : p.next=q.next) : p=q := by
  cases p
  cases q
  congr 1

#print axioms fields
end AspisR1.F3L_AccumulatorExt
