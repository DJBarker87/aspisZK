import Port5Q1_QueryPorts
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_PortUnique
open AspisR1Stage2 OraclePortCheckpointAbiC5

theorem rho (p : verifier.Prepared) (d d' : MatchingSupport.Data E)
    (q q' : Fin 22 → Fin 262144) (r r' : K)
    (h : Port5Q1_QueryPorts.SessionAPrepare p d q r)
    (h' : Port5Q1_QueryPorts.SessionAPrepare p d' q' r') : r=r' :=
  h.rho_eq.symm.trans h'.rho_eq

theorem queries (p : verifier.Prepared) (d d' : MatchingSupport.Data E)
    (q q' : Fin 22 → Fin 262144) (r r' : K)
    (h : Port5Q1_QueryPorts.SessionAPrepare p d q r)
    (h' : Port5Q1_QueryPorts.SessionAPrepare p d' q' r') : q=q' := by
  funext j
  apply Fin.ext
  exact (h.queries j.val j.isLt).symm.trans (h'.queries j.val j.isLt)

theorem no_all_rho (p : verifier.Prepared) (d : MatchingSupport.Data E)
    (q : Fin 22 → Fin 262144) :
    ¬ ∀ r : K, Port5Q1_QueryPorts.SessionAPrepare p d q r := by
  intro all
  exact zero_ne_one (rho p d d q q 0 1 (all 0) (all 1))

#print axioms rho
#print axioms queries
#print axioms no_all_rho
end AspisR1.SAP_PortUnique
end
