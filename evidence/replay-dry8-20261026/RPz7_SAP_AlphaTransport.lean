import RPz7_SAP_CanonicalCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_AlphaTransport
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller.InstalledPreparation
open AspisR1ClaimPreparedBridge AspisR1CurrentPreparedClaim.Concrete

theorem alpha (out : verifier.Prepared) (canonical : CanonicalAlphaPair out) :
    ∀ j : Fin 2,OraclePortCkptAbi4Decode.CanonicalWide (CheckpointBytes3Namespaces.toE
      ((Tx1Q_Carriers.prepared (currentPrepared out)).alpha.val[j.val]'(by
        simpa [(Tx1Q_Carriers.prepared (currentPrepared out)).alpha.property] using j.isLt))) := by
  intro j
  simp only [Tx1Q_Carriers.prepared,currentPrepared,Tx1Q_Carriers.arr,
    AspisR1ClaimPreparedBridge.mapArray,List.getElem_map]
  obtain ⟨a,b,e,ha,hb⟩ := canonical
  simp only [e]
  fin_cases j
  · exact SAP_CanonicalCarrier.wide a ha
  · exact SAP_CanonicalCarrier.wide b hb

#print axioms alpha
end AspisR1.SAP_AlphaTransport
end
