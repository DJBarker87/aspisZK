import F3L_WriterPreparedScalar
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_SourcePrepared
open AspisR1PublicPreparation
open AspisR1CurrentCaller.InstalledPreparation
open AspisR1CurrentPreparedClaim.Concrete AspisR1ClaimPreparedBridge

def alpha (p : verifier.Prepared) (j : Fin 2) : aspis_core.field.WideExact :=
  p.alpha.val[j.val]'(by have h : p.alpha.val.length=2:=p.alpha.property;omega)

def semanticAlpha (p : verifier.Prepared) (j : Fin 10) : aspis_core.field.QM31 :=
  p.semantic_alpha.val[j.val]'(by have h : p.semantic_alpha.val.length=10:=p.semantic_alpha.property;omega)

def point (p : verifier.Prepared) (j : Fin 2) : aspis_core.circle.SecureCirclePoint :=
  p.z.val[j.val]'(by have h : p.z.val.length=2:=p.z.property;omega)

def coordinate (p : verifier.Prepared) (j : Fin 4) : aspis_core.field.QM31 :=
  match j.val with
  | 0 => (point p 0).x
  | 1 => (point p 0).y
  | 2 => (point p 1).x
  | _ => (point p 1).y

/-- Total numeric interpretation of the actual Prepared carrier. The remaining
source/model join must identify these fields with context/data; this definition
does not assert that identification. -/
def numeric (p : verifier.Prepared) : OraclePortCheckpointAbiC5.Prepared where
  state := AspisV8R19.SqueezeOracleBridge.decodeState p.state
  roots := fun j => AspisV8R19.SqueezeOracleBridge.decodeState
    (p.roots.val[j.val]'(by have h : p.roots.val.length=2:=p.roots.property;omega))
  gamma := decode (toClaimE p.gamma)
  kappa := decode (toClaimE p.kappa)
  alpha := fun j=>decode (toClaimE (alpha p j))
  rho := F3L_RhoMeaning.decode p.rho
  queries := CheckpointBytes5Output.queries (Tx1Q_Carriers.prepared (currentPrepared p))
  semanticAlpha := fun j=>F3L_RhoMeaning.decode (semanticAlpha p j)
  coordinates := fun j=>F3L_RhoMeaning.decode (coordinate p j)
  claim := decode (toClaimE p.claim)

end AspisR1.F3L_SourcePrepared
end
