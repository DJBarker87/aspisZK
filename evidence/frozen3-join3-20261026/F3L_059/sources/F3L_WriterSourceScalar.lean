import F3L_WriterNumeric
import F3L_SourceNumeric
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_WriterSourceScalar
open AspisR1CurrentCaller.InstalledPreparation
open AspisR1CurrentPreparedClaim.Concrete AspisR1ClaimPreparedBridge
open OraclePortCkptAbi4Decode OraclePortCkptAbi5Codec

def rawE (x : AspisR1PublicPreparation.aspis_core.field.WideExact) :=
  CheckpointBytes3Namespaces.toE (Tx1Q_Carriers.e (currentE x))
def rawK (x : AspisR1PublicPreparation.aspis_core.field.QM31) :=
  CheckpointBytes3Namespaces.toK (Tx1Q_Carriers.k (currentQ x))

theorem exact_e (x : AspisR1PublicPreparation.aspis_core.field.WideExact)
    (canonical : CanonicalWide (rawE x)) :
    exactE (rawE x) canonical=decode (toClaimE x) := by
  rw [F3L_WriterNumeric.exact_e]
  change CheckpointBytes5Output.ofE (CheckpointBytes3Namespaces.fromE
    (CheckpointBytes3Namespaces.toE (Tx1Q_Carriers.e (currentE x))))=_
  rw [CheckpointBytes3Namespaces.from_to_e,F3L_SourceNumeric.wide]

theorem exact_k (x : AspisR1PublicPreparation.aspis_core.field.QM31)
    (canonical : Canonical (rawK x)) :
    exactK (rawK x) canonical=F3L_RhoMeaning.decode x := by
  rw [F3L_WriterNumeric.exact_k]
  change CheckpointBytes5Output.ofK (CheckpointBytes3Namespaces.fromK
    (CheckpointBytes3Namespaces.toK (Tx1Q_Carriers.k (currentQ x))))=_
  rw [CheckpointBytes3Namespaces.from_to_k,F3L_SourceNumeric.qm]

#print axioms exact_e
#print axioms exact_k
end AspisR1.F3L_WriterSourceScalar
end
