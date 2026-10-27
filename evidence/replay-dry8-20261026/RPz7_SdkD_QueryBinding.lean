import RPz7_SdkC_FirstAuthentication
import Port5Q1_QueryPorts
import RPz7_Tx1Q_Carriers
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_QueryBinding
open Aeneas Aeneas.Std Result

theorem queryAt (raw : Array U32 22#usize) (j : Fin 22) :
    ((raw.val.map UScalar.val)[j.val]?.getD 0) =
      (Port5Q1_GeometryBinding.queryAt raw j.val).val := by
  have len : raw.val.length = 22 := raw.property
  have bound : j.val < raw.val.length := by rw [len]; exact j.isLt
  unfold Port5Q1_GeometryBinding.queryAt
  rw [List.getElem?_map,List.getElem?_eq_getElem bound]
  rfl

theorem prepared (p : AspisR1Stage2.verifier.Prepared)
    (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E)
    (q : Fin 22 → Fin 262144) (rho : OraclePortCheckpointAbiC5.K)
    (prepare : Port5Q1_QueryPorts.SessionAPrepare p data q rho) :
    Port4B_KeyInstall.queries p.queries = q := by
  funext j
  apply Fin.ext
  simp only [Port4B_KeyInstall.queries,queryAt,prepare.queries j.val j.isLt,
    Nat.mod_eq_of_lt (q j).isLt]

theorem current (p : AspisR1CurrentCaller.verifier.Prepared)
    (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E)
    (q : Fin 22 → Fin 262144) (rho : OraclePortCheckpointAbiC5.K)
    (prepare : Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared p) data q rho) :
    Port4B_KeyInstall.queries p.queries = q := prepared _ data q rho prepare

#print axioms queryAt
#print axioms prepared
#print axioms current
end AspisR1.SdkD_QueryBinding
end
