import PV_LIB_A_F166Chains12
import PV_LIB_A_F166Builder12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F166History12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11

def afterPrologue (C : Carrier OWNER Data) (q : State) := PV_THR2_Source166Prologue.after C q

def afterBuilder (C : Carrier OWNER Data) (H : Handler) (q : State) :=
  PV_THR2_Source166BuilderFull.after C H (afterPrologue C q)

def afterCaptures (C : Carrier OWNER Data) (H : Handler) (q : State) :=
  PV_THR2_Source166Captures.after C (afterBuilder C H q)

def steps (C : Carrier OWNER Data) (H : Handler) (q : State) :=
  PV_THR2_Source166Prologue.steps C q +
  PV_THR2_Source166BuilderFull.steps C (afterPrologue C q) +
  PV_THR2_Source166Captures.steps C (afterBuilder C H q) +
  PV_THR2_Source166Enter270.steps C (afterCaptures C H q)

def after (C : Carrier OWNER Data) (H : Handler) (q : State) :=
  PV_THR2_Source166Enter270.after C (afterCaptures C H q)

/-- Continuous166 data path through actual7934 and270 BODY entry, or the
first undefined/native stop. Builder269's full arbitrary reply is retained.
This stops before270 and does not claim a361/14756 or original-entry history. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K (PV_LIB_A_SpawnEnter12.enter270Programs P) resources encode H values
      (steps C H q) ⟨q,none⟩ = ⟨after C H q,none⟩ := by
  unfold steps after afterCaptures afterBuilder afterPrologue
  rw [advance_add,advance_add,advance_add,PV_LIB_A_F166Chains12.prologue]
  have builder := PV_LIB_A_F166Builder12.run C K (PV_THR2_Source270Table.resolve P)
    resources encode H values (PV_THR2_Source166Prologue.after C q)
  change advance C K (PV_LIB_A_SpawnEnter12.enter270Programs P) resources encode H values
    (PV_THR2_Source166BuilderFull.steps C (PV_THR2_Source166Prologue.after C q))
    ⟨PV_THR2_Source166Prologue.after C q,none⟩ = _ at builder
  rw [builder]
  rw [PV_LIB_A_F166Chains12.captures,PV_LIB_A_SpawnEnter12.enter270]

#print axioms afterPrologue
#print axioms afterBuilder
#print axioms afterCaptures
#print axioms steps
#print axioms after
#print axioms run
end PV_LIB_A_F166History12
