import RawTx1DigestLog
import RawDigestLogCarrier

/-! Consumer of the stage-2 log certificate on the exact shared carrier.
Generated tx1/tx2 packages cannot coexist in one Lean environment because they
emit the same global discriminant instance. No carrier conversion is assumed:
the flatten/decode agreement below is definitional. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.Tx1Tx2ConsistentLog
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisR1DigestLogCarrier
open AspisR1PublicPreparation.SourceDigestAddresses

theorem flatten_agreement (input : Slice (Slice U8)) :
    AspisR1DigestLogCarrier.flatten input = AspisV8R19.SqueezeOracleBridge.flatten input := rfl

theorem decode_agreement (output : Array U8 32#usize) :
    AspisR1DigestLogCarrier.decodeState output = AspisV8R19.SqueezeOracleBridge.decodeState output := rfl

/-- Supply tx2Certificate from Tx2DigestLog.log_consistent (in its own generated
package environment). Tx1 actualness is obtained from Tx1DigestLog.log_actual.
This is one Hbytes, not existentially independent transaction oracles. -/
theorem cross_transaction_assembly {H : Type} (D : aspis_core.Digest32 H)
    (Hbytes : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D Hbytes)
    (tr1 tr2 : List (Bytes × State))
    (actual1 : ∀ q ∈ tr1, Tx1DigestLog.ActualPair D q)
    (tx2Certificate : Consistent Hbytes tr2)
    (reached1 reached2 : Bytes × State → Prop)
    (coverage1 : Tx1DigestLog.Tx1InventoryComplete reached1 tr1)
    (coverage2 : Tx1DigestLog.Tx2EmbeddingObligation reached2 tr2) :
    Tx1DigestLog.CrossTransactionConsistency Hbytes tr1 tr2 ∧
    (∀ q, reached1 q ∨ reached2 q → q ∈ tr1 ++ tr2 ∧ q.2 = Hbytes q.1) := by
  have h1 : Consistent Hbytes tr1 := fun q hq => backend q (actual1 q hq)
  have joint := append_consistent Hbytes tr1 tr2 h1 tx2Certificate
  have coverage := append_covers reached1 reached2 tr1 tr2 coverage1 coverage2
  exact ⟨joint,fun q hq => ⟨coverage q hq,joint q (coverage q hq)⟩⟩

theorem cross_transaction_same_address (Hbytes : Bytes → State)
    (tr1 tr2 : List (Bytes × State))
    (joint : Tx1DigestLog.CrossTransactionConsistency Hbytes tr1 tr2)
    (q r : Bytes × State) (hq : q ∈ tr1) (hr : r ∈ tr2) (address : q.1 = r.1) :
    q.2 = r.2 := by
  exact Tx1DigestLog.same_address_same_output Hbytes (tr1 ++ tr2)
    joint q r (List.mem_append_left _ hq) (List.mem_append_right _ hr) address

#print axioms flatten_agreement
#print axioms decode_agreement
#print axioms cross_transaction_assembly
#print axioms cross_transaction_same_address
end AspisR1PublicPreparation.Tx1Tx2ConsistentLog
end
