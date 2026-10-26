import F3L_SourcePrepared
import F3L_SourceNumeric
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_CurrentNumeric
open AspisR1CurrentCaller InstalledPreparation
open AspisV8R19.SqueezeOracleBridge

def alpha (p : verifier.Prepared) (j : Fin 2) : aspis_core.field.wide_exact.WideExact :=
  p.alpha.val[j.val]'(by have h : p.alpha.val.length=2:=p.alpha.property;omega)
def semanticAlpha (p : verifier.Prepared) (j : Fin 10) : aspis_core.field.QM31 :=
  p.semantic_alpha.val[j.val]'(by have h : p.semantic_alpha.val.length=10:=p.semantic_alpha.property;omega)
def point (p : verifier.Prepared) (j : Fin 2) : aspis_core.circle.SecureCirclePoint :=
  p.z.val[j.val]'(by have h : p.z.val.length=2:=p.z.property;omega)
def coordinate (p : verifier.Prepared) (j : Fin 4) : aspis_core.field.QM31 :=
  match j.val with
  | 0 => (point p 0).x | 1 => (point p 0).y | 2 => (point p 1).x | _ => (point p 1).y

def numeric (p : verifier.Prepared) : OraclePortCheckpointAbiC5.Prepared where
  state := decodeState p.state
  roots := fun j=>decodeState (p.roots.val[j.val]'(by have h : p.roots.val.length=2:=p.roots.property;omega))
  gamma := CheckpointBytes5Output.ofE (Tx1Q_Carriers.e p.gamma)
  kappa := CheckpointBytes5Output.ofE (Tx1Q_Carriers.e p.kappa)
  alpha := fun j=>CheckpointBytes5Output.ofE (Tx1Q_Carriers.e (alpha p j))
  rho := CheckpointBytes5Output.ofK (Tx1Q_Carriers.k p.rho)
  queries := CheckpointBytes5Output.queries (Tx1Q_Carriers.prepared p)
  semanticAlpha := fun j=>CheckpointBytes5Output.ofK (Tx1Q_Carriers.k (semanticAlpha p j))
  coordinates := fun j=>CheckpointBytes5Output.ofK (Tx1Q_Carriers.k (coordinate p j))
  claim := CheckpointBytes5Output.ofE (Tx1Q_Carriers.e p.claim)
end AspisR1.SAP_CurrentNumeric
end
