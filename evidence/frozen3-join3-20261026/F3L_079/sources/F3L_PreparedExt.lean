import OraclePortCheckpointAbiC5
set_option autoImplicit false
namespace AspisR1.F3L_PreparedExt

theorem fields (p q : OraclePortCheckpointAbiC5.Prepared)
    (state : p.state=q.state) (roots : p.roots=q.roots)
    (gamma : p.gamma=q.gamma) (kappa : p.kappa=q.kappa)
    (alpha : p.alpha=q.alpha) (rho : p.rho=q.rho) (queries : p.queries=q.queries)
    (semanticAlpha : p.semanticAlpha=q.semanticAlpha) (coordinates : p.coordinates=q.coordinates)
    (claim : p.claim=q.claim) : p=q := by
  cases p
  cases q
  congr 1

#print axioms fields
end AspisR1.F3L_PreparedExt
