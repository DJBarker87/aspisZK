import PV_LIB_A_SpawnEnter12
import PV_THR2_Source166BuilderFull
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F166Builder12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11
open PV_LIB_A_SpawnEnter12

theorem waiting (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet (spawnPrograms P) ⟨⟨.running (PV_THR2_IntrinsicFrameEnter.pending s a parents loops
      (PV_THR2_F166.live.body.drop 7) PV_THR2_SourceSpawnTable.fn269 [] 4),w,es⟩,stack⟩ := by
  constructor
  · intro c hc; cases hc
    unfold sourceSelect
    change (match spawnPrograms P PV_THR2_SourceSpawnTable.fn269 with
      | some _ => none
      | none => (v2Source PV_THR2_SourceSpawnTable.fn269).bind _) = none
    rw [show spawnPrograms P PV_THR2_SourceSpawnTable.fn269 = none from
      PV_THR2_SourceSpawnTable.child269 P]
    rfl
  · intro c hc; cases hc; exact ⟨rfl,rfl,True.intro⟩

theorem trace (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Handler) (q : State) :
    Trace C K (spawnPrograms P) H (PV_THR2_Source166BuilderFull.steps C q) q := by
  apply PV_LIB_A_Continuation12.trace
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change Trace C K (spawnPrograms P) H 2
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F166.node6 :: PV_THR2_F166.live.body.drop 7,loops := loops},parents,s⟩,w,es⟩,stack⟩
  apply PV_LIB_A_RangeStartTrace11.cons_run C K _ H 1 _ _
    (PV_LIB_A_StructuredTrace12.issue_quiet _ s a parents loops _
      PV_THR2_Source166BuilderFull.source.1 _ [] 4 (by decide) w es stack)
    (PV_THR2_IntrinsicFrameSteps.call C K _ H s s a parents loops _
      PV_THR2_Source166BuilderFull.source.1 PV_THR2_Source166BuilderFull.source.2.1
      PV_THR2_Source166BuilderFull.source.2.2 [] [] 4 w es stack (by rfl))
  exact ⟨waiting P s a parents loops w es stack,True.intro⟩

/-- Actual7916 issues and consumes the full Builder269 reply. No constructor
success/value/world assumption, including on pending/failure/divergence. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K (spawnPrograms P) resources encode H values (PV_THR2_Source166BuilderFull.steps C q) ⟨q,none⟩ =
      ⟨PV_THR2_Source166BuilderFull.after C H q,none⟩ := by
  rw [PV_LIB_A_PrefixMachine11.run C K _ resources encode H values _ _ (trace C K P H q)]
  exact congrArg (fun q => (⟨q,none⟩ : SourceState)) (PV_THR2_Source166BuilderFull.run C K P H q)

#print axioms waiting
#print axioms trace
#print axioms run
end PV_LIB_A_F166Builder12
