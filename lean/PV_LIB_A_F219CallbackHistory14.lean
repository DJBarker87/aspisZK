import PV_LIB_A_F219Enter31614
import PV_LIB_A_SourceContinuation12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F219CallbackHistory14
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_LIB_StoreActionTable PV_THR2_SourceStoreLibrary PV_LIB_A_PrefixMachine11
open PV_LIB_A_SourceSequence13 PV_LIB_A_SequenceFrontier13

def seq : Seq := prepend PV_THR2_F219.node6 (prepend PV_THR2_F219.node7
  (prepend PV_THR2_F219.node8 (prepend PV_THR2_F219.node9 (prepend PV_THR2_F219.node10 .done))))
theorem shape : nodes seq ++ PV_THR2_F219.live.body.drop 11 = PV_THR2_F219.live.body.drop 6 := rfl
theorem off : sites seq := by
  change (219 : Nat) ≠ 361 ∧ (219 : Nat) ≠ 361 ∧ (219 : Nat) ≠ 361 ∧ (219 : Nat) ≠ 361 ∧ (219 : Nat) ≠ 361 ∧ True
  decide
abbrev cost1 (C : Carrier OWNER Data) := PV_LIB_A_SequenceFrontier13.steps C seq (PV_THR2_F219.live.body.drop 11)
abbrev finish1 (C : Carrier OWNER Data) := PV_LIB_A_SequenceFrontier13.after C seq (PV_THR2_F219.live.body.drop 11)
def stage1 (C : Carrier OWNER Data) := PV_LIB_A_SourceContinuation12.after (finish1 C)
def after (C : Carrier OWNER Data) (q : SourceState) :=
  PV_LIB_A_SourceContinuation12.after PV_LIB_A_F219Enter31614.after (stage1 C q)
def steps (C : Carrier OWNER Data) (q : SourceState) :=
  PV_LIB_A_SourceContinuation12.steps (cost1 C) q +
  PV_LIB_A_SourceContinuation12.steps PV_LIB_A_F219Enter31614.steps (stage1 C q)

/-- Full post134 source continuation through actual9196/316 or the first source
gap. The aggregate move's missing-value arm remains explicit. -/
theorem run (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : SourceState) :
    PV_LIB_A_PrefixMachine11.advance (PV_THR2_EntryDynamic.carrier C b) K (PV_THR2_CatchChildren.table P)
      resources encode H values (steps (PV_THR2_EntryDynamic.carrier C b) q) q =
      after (PV_THR2_EntryDynamic.carrier C b) q := by
  unfold steps after
  rw [advance_add,PV_LIB_A_SourceContinuation12.run _ K (PV_THR2_CatchChildren.table P) resources encode H values _ _
    (PV_LIB_A_SequenceFrontier13.run _ K (PV_THR2_CatchChildren.table P) resources encode H values seq _ off)]
  exact PV_LIB_A_SourceContinuation12.run _ K _ resources encode H values _ _
    (PV_LIB_A_F219Enter31614.run C b K P resources encode H values) _

#print axioms shape
#print axioms off
#print axioms after
#print axioms steps
#print axioms run
end PV_LIB_A_F219CallbackHistory14
