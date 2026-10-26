import F3K_CheckpointQueryNumeric
import Port5Q1_QueryPorts
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_PreparedQueryPort

theorem queries (p : AspisR1Stage2.verifier.Prepared)
    (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E)
    (q : Fin 22 → Fin 262144) (rho : OraclePortCheckpointAbiC5.K)
    (port : Port5Q1_QueryPorts.SessionAPrepare p data q rho) : CheckpointBytes5Output.queries p=q := by
  apply F3K_CheckpointQueryNumeric.exact_queries p q
  intro j
  have bound : j.val<p.queries.val.length := by have h : p.queries.val.length=22:=p.queries.property;omega
  have cell := port.queries j.val j.isLt
  simpa only [Port5Q1_GeometryBinding.queryAt,List.getElem?_eq_getElem bound,Option.getD_some] using cell

#print axioms queries
end AspisR1.F3L_PreparedQueryPort
end
