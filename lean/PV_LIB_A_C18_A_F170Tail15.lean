import PV_LIB_A_V2Frontiers14
import PV_THR2_F170
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F170Tail15
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary PV_LIB_StoreActionTable
open PV_LIB_A_SourceSequence13 PV_LIB_A_SequenceFrontier13

/-- No available f170 contract supplies this successor on the context-bound
original v2. These are its nine source nodes after the returned TLS callback;
no callee, native reply, loop, or destructor is unfolded here. -/
def seq : Seq := prepend PV_THR2_F170.node56 (prepend PV_THR2_F170.node57 (prepend PV_THR2_F170.node58 (prepend PV_THR2_F170.node59 (prepend PV_THR2_F170.node60 (prepend PV_THR2_F170.node61 (prepend PV_THR2_F170.node62 (prepend PV_THR2_F170.node63 (prepend PV_THR2_F170.node64 (.done)))))))))

theorem shape : nodes seq ++ PV_THR2_F170.live.body.drop 49 =
    PV_THR2_F170.live.body.drop 40 := rfl

theorem off : sites seq := by
  change (170 : Nat) ≠ 361 ∧ (170 : Nat) ≠ 361 ∧ (170 : Nat) ≠ 361 ∧ (170 : Nat) ≠ 361 ∧ (170 : Nat) ≠ 361 ∧ (170 : Nat) ≠ 361 ∧ (170 : Nat) ≠ 361 ∧ (170 : Nat) ≠ 361 ∧ (170 : Nat) ≠ 361 ∧ True
  decide

/-- Exact v2 continuation, retaining a missing aggregate/read as its actual
undefined state. This intermediate segment is not an OriginalToF6 inhabitant. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    let q : State := ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 40},parents,s⟩,w,es⟩,stack⟩
    PV_LIB_StoreActionTable.advance C K P resources encode H values (steps C a w seq s) q =
      ⟨⟨result C a parents [] (PV_THR2_F170.live.body.drop 49) w seq s,w,es⟩,stack⟩ := by
  dsimp only
  rw [← shape]
  rw [PV_LIB_A_V2TraceTransport14.run C K P resources encode H values _ _
    (certified C K P H seq s a parents [] _ w es stack off).1]
  exact (certified C K P H seq s a parents [] _ w es stack off).2

#print axioms shape
#print axioms off
#print axioms run
end PV_LIB_A_F170Tail15
