import PV_LIB_A_SequenceFrontier13
import PV_THR2_Source208Table
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F208Prefix14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11
open PV_LIB_A_SourceSequence13 PV_LIB_A_SequenceFrontier13

def seq : Seq := prepend PV_THR2_F208.node0 (prepend PV_THR2_F208.node1 (prepend PV_THR2_F208.node2 (prepend PV_THR2_F208.node3 (prepend PV_THR2_F208.node4 (prepend PV_THR2_F208.node5 (prepend PV_THR2_F208.node6 (prepend PV_THR2_F208.node7 (prepend PV_THR2_F208.node8 (prepend PV_THR2_F208.node9 (prepend PV_THR2_F208.node10 (.done)))))))))))
theorem shape : nodes seq ++ PV_THR2_F208.live.body.drop 11 = PV_THR2_F208.live.body := rfl
theorem off : sites seq := by
  change (208 : Nat) ≠ 361 ∧ (208 : Nat) ≠ 361 ∧ (208 : Nat) ≠ 361 ∧ (208 : Nat) ≠ 361 ∧ (208 : Nat) ≠ 361 ∧ (208 : Nat) ≠ 361 ∧ (208 : Nat) ≠ 361 ∧ (208 : Nat) ≠ 361 ∧ (208 : Nat) ≠ 361 ∧ (208 : Nat) ≠ 361 ∧ (208 : Nat) ≠ 361 ∧ True
  decide

def steps (C : Carrier OWNER Data) := PV_LIB_A_SequenceFrontier13.steps C seq (PV_THR2_F208.live.body.drop 11)
def after (C : Carrier OWNER Data) := PV_LIB_A_SequenceFrontier13.after C seq (PV_THR2_F208.live.body.drop 11)

/-- Actual emitted source preparations; malformed/missing captures retain their
source gaps. No successful native reply or capture readback is assumed. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K P resources encode H values (steps C q) ⟨q,none⟩ = ⟨after C q,none⟩ :=
  PV_LIB_A_SequenceFrontier13.run C K P resources encode H values seq _ off q

#print axioms shape
#print axioms off
#print axioms run
end PV_LIB_A_F208Prefix14
