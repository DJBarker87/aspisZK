import PV_LIB_A_StructuredTrace12
import PV_THR2_Source15SpawnEnter
import PV_THR2_Source166Enter270
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_SpawnEnter12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11

def spawnPrograms (P : Data → Option PV_STX2_SliceSyntax.Program) := PV_THR2_Source208Table.table (PV_THR2_Source15Table.resolve (PV_THR2_OwnInitChildren.resolve (PV_THR2_SourceSpawnTable.resolve P)))

theorem spawn_trace (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Handler) (q : State) :
    Trace C K (spawnPrograms P) H (PV_THR2_Source15SpawnEnter.steps C q) q := by
  apply PV_LIB_A_Continuation12.trace
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change Trace C K (spawnPrograms P) H
    (PV_THR2_IntrinsicStructuredCall.steps C s a PV_THR2_Source15SpawnEnter.source.2.2.2.1 w)
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.node35 :: PV_THR2_F15.block47.drop 21,loops := loops},parents,s⟩,w,es⟩,stack⟩
  exact PV_LIB_A_StructuredTrace12.trace C K _ H s a parents loops _
    PV_THR2_Source15SpawnEnter.source.1 PV_THR2_Source15SpawnEnter.source.2.1 PV_THR2_Source15SpawnEnter.source.2.2.1
    PV_THR2_Source15SpawnEnter.source.2.2.2.1 PV_THR2_Source15SpawnEnter.source.2.2.2.2 PV_THR2_F166.live
    (by decide) (by intro t vs; cases vs with | nil => rfl | cons v vs => cases vs <;> rfl) (by intro t vs; cases vs with | nil => rfl | cons v vs => cases vs <;> rfl) w es stack (by rfl) (PV_THR2_SourceSpawnTable.at166 P)

/-- Actual source call enters its structured data-path body on the corrected
machine. Failed operands retain their source gap and saved frames. -/
theorem spawn (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K (spawnPrograms P) resources encode H values (PV_THR2_Source15SpawnEnter.steps C q) ⟨q,none⟩ =
      ⟨PV_THR2_Source15SpawnEnter.after C q,none⟩ := by
  rw [PV_LIB_A_PrefixMachine11.run C K _ resources encode H values _ _ (spawn_trace C K P H q)]
  exact congrArg (fun q => (⟨q,none⟩ : SourceState)) (PV_THR2_Source15SpawnEnter.run C K P H q)

def enter270Programs (P : Data → Option PV_STX2_SliceSyntax.Program) := PV_THR2_Source208Table.table (PV_THR2_Source15Table.resolve (PV_THR2_OwnInitChildren.resolve (PV_THR2_SourceSpawnTable.resolve (PV_THR2_Source270Table.resolve P))))

theorem enter270_trace (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Handler) (q : State) :
    Trace C K (enter270Programs P) H (PV_THR2_Source166Enter270.steps C q) q := by
  apply PV_LIB_A_Continuation12.trace
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change Trace C K (enter270Programs P) H
    (PV_THR2_IntrinsicStructuredCall.steps C s a PV_THR2_Source166Enter270.source.2.2.2.1 w)
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F166.node12 :: PV_THR2_F166.live.body.drop 13,loops := loops},parents,s⟩,w,es⟩,stack⟩
  exact PV_LIB_A_StructuredTrace12.trace C K _ H s a parents loops _
    PV_THR2_Source166Enter270.source.1 PV_THR2_Source166Enter270.source.2.1 PV_THR2_Source166Enter270.source.2.2.1
    PV_THR2_Source166Enter270.source.2.2.2.1 PV_THR2_Source166Enter270.source.2.2.2.2 PV_THR2_F270.live
    (by decide) (by intro t vs; cases vs with | nil => rfl | cons v vs => cases vs <;> rfl) (by intro t vs; cases vs with | nil => rfl | cons v vs => cases vs <;> rfl) w es stack (by rfl) (PV_THR2_Source270Table.at270 P)

/-- Actual source call enters its structured data-path body on the corrected
machine. Failed operands retain their source gap and saved frames. -/
theorem enter270 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K (enter270Programs P) resources encode H values (PV_THR2_Source166Enter270.steps C q) ⟨q,none⟩ =
      ⟨PV_THR2_Source166Enter270.after C q,none⟩ := by
  rw [PV_LIB_A_PrefixMachine11.run C K _ resources encode H values _ _ (enter270_trace C K P H q)]
  exact congrArg (fun q => (⟨q,none⟩ : SourceState)) (PV_THR2_Source166Enter270.run C K P H q)

#print axioms spawnPrograms
#print axioms spawn_trace
#print axioms spawn
#print axioms enter270Programs
#print axioms enter270_trace
#print axioms enter270
end PV_LIB_A_SpawnEnter12
