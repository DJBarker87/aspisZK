from pathlib import Path
common='''set_option autoImplicit false
noncomputable section
namespace NAMESPACE
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11
'''
for name,mod,node,rest,body in [
 ('F6Enter125','PV_THR2_F6',45,'PV_THR2_F6.live.body.drop 46','PV_THR2_F125.live'),
 ('F125Enter219','PV_THR2_F125',3,'PV_THR2_F125.live.body.drop 4','PV_THR2_F219.live')]:
 ns='PV_LIB_A_'+name+'13'
 s='import PV_LIB_A_StructuredFrontier13\nimport PV_THR2_CatchChildren\n'+common.replace('NAMESPACE',ns)
 s+=f'''
def programs := PV_THR2_CatchChildren.table
def src := PV_LIB_A_StructuredFrontier13.source {mod}.node{node}
def rest := {rest}

theorem shape : PV_LIB_A_StructuredFrontier13.node src :: rest = {mod}.live.body.drop {node} := rfl

def steps (C : Carrier OWNER Data) := PV_LIB_A_StructuredFrontier13.steps C src rest
def after (C : Carrier OWNER Data) := PV_LIB_A_StructuredFrontier13.after C src rest {body}

/-- Actual emitted structured entry with every missing-operand case retained.
No captured value, child activation, successful native reply or desired store is supplied. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K (programs P) resources encode H values (steps C q) ⟨q,none⟩ = ⟨after C q,none⟩ := by
  apply PV_LIB_A_StructuredFrontier13.run
  · decide
  · intro t a parents loops vs
    cases vs with
    | nil => exact ⟨rfl,rfl⟩
    | cons v vs => cases vs <;> exact ⟨rfl,rfl⟩
  · intro t a parents loops vs
    apply PV_THR2_IntrinsicFrameOrdinary.run
    intro eq
    have ids := congrArg PV_THR2_OffPath.functionId eq
    cases ids
  · intro s a w; rfl
  · rfl

#print axioms programs
#print axioms shape
#print axioms steps
#print axioms after
#print axioms run
end {ns}
'''
 s=s.replace('import PV_THR2_CatchChildren','import PV_THR2_CatchChildren\nimport PV_THR2_IntrinsicFrameOrdinary')
 Path('lean',ns+'.lean').write_text(s)
# Actual125 prologue; exact shape rules out parser fallback.
ns='PV_LIB_A_F125Prologue13'
s='import PV_LIB_A_SequenceFrontier13\nimport PV_THR2_CatchChildren\n'+common.replace('NAMESPACE',ns)
s+='''open PV_LIB_A_SourceSequence13 PV_LIB_A_SequenceFrontier13

def seq : Seq := prepend PV_THR2_F125.node0 (prepend PV_THR2_F125.node1 (prepend PV_THR2_F125.node2 .done))
theorem shape : nodes seq ++ PV_THR2_F125.live.body.drop 3 = PV_THR2_F125.live.body := rfl
theorem off : sites seq := by
  change (125 : Nat) ≠ 361 ∧ (125 : Nat) ≠ 361 ∧ (125 : Nat) ≠ 361 ∧ True
  decide

def steps (C : Carrier OWNER Data) := PV_LIB_A_SequenceFrontier13.steps C seq (PV_THR2_F125.live.body.drop 3)
def after (C : Carrier OWNER Data) := PV_LIB_A_SequenceFrontier13.after C seq (PV_THR2_F125.live.body.drop 3)

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
end PV_LIB_A_F125Prologue13
'''
Path('lean',ns+'.lean').write_text(s)
