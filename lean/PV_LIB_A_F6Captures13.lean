import PV_LIB_A_SequenceFrontier13
import PV_LIB_A_F6History12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F6Captures13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11 PV_LIB_A_SourceSequence13
open PV_LIB_A_SequenceFrontier13

/-- Actual post124 scope, PhantomData and captured AssertUnwindSafe construction.
These are source moves/storage administration before1989, not destructor cleanup. -/
def seq : Seq :=
  prepend PV_THR2_F6.node26 (prepend PV_THR2_F6.node27 (prepend PV_THR2_F6.node28 (prepend PV_THR2_F6.node29 (prepend PV_THR2_F6.node30 (prepend PV_THR2_F6.node31 (prepend PV_THR2_F6.node32 (prepend PV_THR2_F6.node33 (prepend PV_THR2_F6.node34 (prepend PV_THR2_F6.node35 (prepend PV_THR2_F6.node36 (prepend PV_THR2_F6.node37 (prepend PV_THR2_F6.node38 (prepend PV_THR2_F6.node39 (prepend PV_THR2_F6.node40 (prepend PV_THR2_F6.node41 (prepend PV_THR2_F6.node42 (prepend PV_THR2_F6.node43 (prepend PV_THR2_F6.node44 (.done)))))))))))))))))))

theorem shape : nodes seq ++ PV_THR2_F6.live.body.drop 45 = PV_THR2_F6.live.body.drop 26 := rfl

theorem off : sites seq := by
  change (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ True
  decide

def steps (C : Carrier OWNER Data) := PV_LIB_A_SequenceFrontier13.steps C seq (PV_THR2_F6.live.body.drop 45)
def after (C : Carrier OWNER Data) := PV_LIB_A_SequenceFrontier13.after C seq (PV_THR2_F6.live.body.drop 45)

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
end PV_LIB_A_F6Captures13
