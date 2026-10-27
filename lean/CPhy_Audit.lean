import CPhy_Physical
import WAdm_Nonvacuity
import SdkD_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPhy_Audit
open Aeneas Aeneas.Std Result

/-- Exact joint/Tx1Q dictionary identity; no compatibility premise. -/
theorem dictionary_compatibility {C : Type} (adapter : AdapterRw.Ops)
    (ops : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :
    ClaimsUnrolledSdk.sdkOps adapter (Uni_Install.current ops reserved query geo) B std =
      ClaimsUnrolledSdk.sdkOps adapter
        (Tx1Q_SameCut.dictionary (Op5T_Concrete.current ops) reserved query geo) B std := by
  rw [Uni_Install.compose_tx1]

/-- The source range/scan witness class is inhabited, with the SAME y1
passed to check_values and all six installed nodeSlot returns. This is a
local physical fixture, not a cryptographic SDK accepted pair. -/
theorem physical_fixture :
    S2W_ChildJoins.MultiproofConeJoin Op3I_Witness.proof Op3I_Witness.proof
      (CPhy_Ranges.nodes Op3I_Witness.proof Op3I_Witness.proof) ∧
    S2W_ChildJoins.S8StageConeJoin Op3I_Witness.proof (CPhy_Ranges.y1 Op3I_Witness.proof) ∧
    Op4P_Extract.Op4P_reference.reference.check_values (CPhy_Ranges.y1 Op3I_Witness.proof) = ok true ∧
    ∀ (batch kind : Nat) (hb : batch < 2) (hk : kind < 3),
      Port4B_Install.leaves.op3 Op3I_Witness.proof
        (Usize.ofNat (3*batch+kind) (by scalar_tac)) =
      ok (CPhy_Ranges.nodes Op3I_Witness.proof Op3I_Witness.proof batch kind) := by
  have scanned := CPhy_Ranges.scan Op3I_Witness.proof Op3I_Witness.fields.1 Op4P_Audit.witness_success.2
  refine ⟨CPhy_Ranges.multiproof _ _ Op3I_Witness.fields.1 Op3I_Witness.fields.1,
    scanned.1,scanned.2,?_⟩
  intro batch kind hb hk
  simpa only [CPhy_Ranges.nodes,ite_self] using
    (CPhy_Ranges.physical Op3I_Witness.proof Op3I_Witness.fields.1 batch kind hb hk).2

#print axioms dictionary_compatibility
#print axioms physical_fixture
#print axioms CPhy_Accepted.accepted_pair_unified
#print axioms CPhy_HeaderCells.selector
#print axioms CPhy_HeaderCells.proofHash
#print axioms CPhy_HeaderCells.publicHash
#print axioms CPhy_Header.decode_fields
#print axioms CPhy_Header.writer
#print axioms CPhy_Header.reader
#print axioms CPhy_Ranges.physical
#print axioms CPhy_Ranges.multiproof
#print axioms CPhy_Ranges.scan
#print axioms CPhy_Physical.accepted_pair_unified
#print axioms WAdm_Nonvacuity.domain_nonempty
#print axioms SdkD_Nonvacuity.instance_exists
#print CPhy_Header.decode
#print S2W_AuthenticatedInputs.CheckpointWriterConeJoin
#print S2W_AuthenticatedInputs.CheckpointReaderConeJoin
#print S2Y_OwnedChildren.PhysicalRange
#print S2Y_OwnedChildren.Y1Range
end AspisR1.CPhy_Audit
end
