import RPz7_F3L_RhoCanonical
import RPz7_WAdm_Domain
import RPz7_CurrentPreparedInstalledMeaning
set_option autoImplicit false
namespace AspisR1.SAP_CanonicalCarrier
open AspisR1CurrentCaller.InstalledPreparation
open AspisR1PublicPreparation
open AspisR1CurrentPreparedClaim.Concrete AspisR1ClaimPreparedBridge

def CanonK (q : aspis_core.field.QM31) : Prop :=
  q.c0.a.val<2147483647 ∧ q.c0.b.val<2147483647 ∧
  q.c1.a.val<2147483647 ∧ q.c1.b.val<2147483647

theorem wide (x : aspis_core.field.WideExact) (h : Canonical (toClaimE x)) :
    OraclePortCkptAbi4Decode.CanonicalWide
      (CheckpointBytes3Namespaces.toE (Tx1Q_Carriers.e (currentE x))) := by
  rcases h with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩
  exact ⟨⟨a,b,c,d⟩,⟨e,f,g,h⟩⟩

theorem qm (x : aspis_core.field.QM31) (h : CanonK x) :
    OraclePortCkptAbi4Decode.Canonical
      (CheckpointBytes3Namespaces.toK (Tx1Q_Carriers.k (currentQ x))) := by
  exact h

#print axioms wide
#print axioms qm
end AspisR1.SAP_CanonicalCarrier
