import PV_LIB_A_SequenceFrontier13
import PV_THR2_CatchChildren
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F316Prefix13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11
open PV_LIB_A_SourceSequence13 PV_LIB_A_SequenceFrontier13

def seq : Seq := prepend PV_THR2_F316.node0 (prepend PV_THR2_F316.node1 (prepend PV_THR2_F316.node2 (prepend PV_THR2_F316.node3 (prepend PV_THR2_F316.node4 (prepend PV_THR2_F316.node5 (prepend PV_THR2_F316.node6 (.done)))))))
theorem shape : nodes seq ++ PV_THR2_F316.live.body.drop 7 = PV_THR2_F316.live.body := rfl
theorem off : sites seq := by
  change (316 : Nat) ≠ 361 ∧ (316 : Nat) ≠ 361 ∧ (316 : Nat) ≠ 361 ∧ (316 : Nat) ≠ 361 ∧ (316 : Nat) ≠ 361 ∧ (316 : Nat) ≠ 361 ∧ (316 : Nat) ≠ 361 ∧ True
  decide

def steps (C : Carrier OWNER Data) := PV_LIB_A_SequenceFrontier13.steps C seq (PV_THR2_F316.live.body.drop 7)
def after (C : Carrier OWNER Data) := PV_LIB_A_SequenceFrontier13.after C seq (PV_THR2_F316.live.body.drop 7)

theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K P resources encode H values (steps C q) ⟨q,none⟩ = ⟨after C q,none⟩ :=
  PV_LIB_A_SequenceFrontier13.run C K P resources encode H values seq _ off q

#print axioms shape
#print axioms off
#print axioms steps
#print axioms after
#print axioms run
end PV_LIB_A_F316Prefix13
