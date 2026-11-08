import PV_LIB_A_SequenceFrontier13
import PV_LIB_A_PrefixNativeCalls14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F6SourceSequences14
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_LIB_StoreActionTable PV_THR2_SourceStoreLibrary PV_LIB_A_PrefixMachine11
open PV_LIB_A_SourceSequence13 PV_LIB_A_SequenceFrontier13

def seqA : Seq := prepend PV_THR2_F6.node0 (prepend PV_THR2_F6.node1 (prepend PV_THR2_F6.node2 (prepend PV_THR2_F6.node3 (prepend PV_THR2_F6.node4 (prepend PV_THR2_F6.node5 (prepend PV_THR2_F6.node6 (prepend PV_THR2_F6.node7 (prepend PV_THR2_F6.node8 (prepend PV_THR2_F6.node9 (prepend PV_THR2_F6.node10 (prepend PV_THR2_F6.node11 (prepend PV_THR2_F6.node12 (prepend PV_THR2_F6.node13 (prepend PV_THR2_F6.node14 (prepend PV_THR2_F6.node15 (.done))))))))))))))))
theorem shapeA : nodes seqA ++ PV_THR2_F6.live.body.drop 16 = PV_THR2_F6.live.body.drop 0 := rfl
theorem offA : sites seqA := by
  change (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ True
  decide

def stepsA (C : Carrier OWNER Data) := PV_LIB_A_SequenceFrontier13.steps C seqA (PV_THR2_F6.live.body.drop 16)
def afterA (C : Carrier OWNER Data) := PV_LIB_A_SequenceFrontier13.after C seqA (PV_THR2_F6.live.body.drop 16)
theorem runA (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K P resources encode H values (stepsA C q) ⟨q,none⟩ = ⟨afterA C q,none⟩ :=
  PV_LIB_A_SequenceFrontier13.run C K P resources encode H values seqA _ offA q

#print axioms shapeA
#print axioms offA
#print axioms runA

def seqB : Seq := prepend PV_THR2_F6.node17 (.done)
theorem shapeB : nodes seqB ++ PV_THR2_F6.live.body.drop 18 = PV_THR2_F6.live.body.drop 17 := rfl
theorem offB : sites seqB := by
  change (6 : Nat) ≠ 361 ∧ True
  decide

def stepsB (C : Carrier OWNER Data) := PV_LIB_A_SequenceFrontier13.steps C seqB (PV_THR2_F6.live.body.drop 18)
def afterB (C : Carrier OWNER Data) := PV_LIB_A_SequenceFrontier13.after C seqB (PV_THR2_F6.live.body.drop 18)
theorem runB (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K P resources encode H values (stepsB C q) ⟨q,none⟩ = ⟨afterB C q,none⟩ :=
  PV_LIB_A_SequenceFrontier13.run C K P resources encode H values seqB _ offB q

#print axioms shapeB
#print axioms offB
#print axioms runB

def seqC : Seq := prepend PV_THR2_F6.node19 (.done)
theorem shapeC : nodes seqC ++ PV_THR2_F6.live.body.drop 20 = PV_THR2_F6.live.body.drop 19 := rfl
theorem offC : sites seqC := by
  change (6 : Nat) ≠ 361 ∧ True
  decide

def stepsC (C : Carrier OWNER Data) := PV_LIB_A_SequenceFrontier13.steps C seqC (PV_THR2_F6.live.body.drop 20)
def afterC (C : Carrier OWNER Data) := PV_LIB_A_SequenceFrontier13.after C seqC (PV_THR2_F6.live.body.drop 20)
theorem runC (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K P resources encode H values (stepsC C q) ⟨q,none⟩ = ⟨afterC C q,none⟩ :=
  PV_LIB_A_SequenceFrontier13.run C K P resources encode H values seqC _ offC q

#print axioms shapeC
#print axioms offC
#print axioms runC

def seqD : Seq := prepend PV_THR2_F6.node21 (prepend PV_THR2_F6.node22 (prepend PV_THR2_F6.node23 (prepend PV_THR2_F6.node24 (.done))))
theorem shapeD : nodes seqD ++ PV_THR2_F6.live.body.drop 25 = PV_THR2_F6.live.body.drop 21 := rfl
theorem offD : sites seqD := by
  change (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ True
  decide

def stepsD (C : Carrier OWNER Data) := PV_LIB_A_SequenceFrontier13.steps C seqD (PV_THR2_F6.live.body.drop 25)
def afterD (C : Carrier OWNER Data) := PV_LIB_A_SequenceFrontier13.after C seqD (PV_THR2_F6.live.body.drop 25)
theorem runD (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K P resources encode H values (stepsD C q) ⟨q,none⟩ = ⟨afterD C q,none⟩ :=
  PV_LIB_A_SequenceFrontier13.run C K P resources encode H values seqD _ offD q

#print axioms shapeD
#print axioms offD
#print axioms runD

def seqE : Seq := prepend PV_THR2_F6.node26 (prepend PV_THR2_F6.node27 (prepend PV_THR2_F6.node28 (prepend PV_THR2_F6.node29 (prepend PV_THR2_F6.node30 (prepend PV_THR2_F6.node31 (prepend PV_THR2_F6.node32 (prepend PV_THR2_F6.node33 (prepend PV_THR2_F6.node34 (prepend PV_THR2_F6.node35 (prepend PV_THR2_F6.node36 (prepend PV_THR2_F6.node37 (prepend PV_THR2_F6.node38 (prepend PV_THR2_F6.node39 (prepend PV_THR2_F6.node40 (prepend PV_THR2_F6.node41 (prepend PV_THR2_F6.node42 (prepend PV_THR2_F6.node43 (prepend PV_THR2_F6.node44 (.done)))))))))))))))))))
theorem shapeE : nodes seqE ++ PV_THR2_F6.live.body.drop 45 = PV_THR2_F6.live.body.drop 26 := rfl
theorem offE : sites seqE := by
  change (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ True
  decide

def stepsE (C : Carrier OWNER Data) := PV_LIB_A_SequenceFrontier13.steps C seqE (PV_THR2_F6.live.body.drop 45)
def afterE (C : Carrier OWNER Data) := PV_LIB_A_SequenceFrontier13.after C seqE (PV_THR2_F6.live.body.drop 45)
theorem runE (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K P resources encode H values (stepsE C q) ⟨q,none⟩ = ⟨afterE C q,none⟩ :=
  PV_LIB_A_SequenceFrontier13.run C K P resources encode H values seqE _ offE q

#print axioms shapeE
#print axioms offE
#print axioms runE
end PV_LIB_A_F6SourceSequences14
