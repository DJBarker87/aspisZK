import PV_LIB_A_ClosureAggregate12
import PV_LIB_A_F166History12
import PV_LIB_A_SourceContinuation12
import PV_LIB_A_RangeHistory12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_Post93Prefix12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11

abbrev liftedSteps := PV_LIB_A_SourceContinuation12.steps
abbrev liftedAfter := PV_LIB_A_SourceContinuation12.after

def aggregateAfter (C : Carrier OWNER Data) (q : SourceState) :=
  liftedAfter (PV_THR2_Source15ClosureAggregate.after C) q

def spawnAfter (C : Carrier OWNER Data) (q : SourceState) :=
  liftedAfter (PV_THR2_Source15SpawnEnter.after C) (aggregateAfter C q)

def steps (C : Carrier OWNER Data) (H : Handler) (q : SourceState) :=
  liftedSteps PV_THR2_Source15ClosureAggregate.steps q +
  liftedSteps (PV_THR2_Source15SpawnEnter.steps C) (aggregateAfter C q) +
  liftedSteps (PV_LIB_A_F166History12.steps C H) (spawnAfter C q)

def after (C : Carrier OWNER Data) (H : Handler) (q : SourceState) :=
  liftedAfter (PV_LIB_A_F166History12.after C H) (spawnAfter C q)

/-- Exact post93 capture frontier through closure3472, spawn3490,166 and270
entry. Failed/None/unrelated frontiers stay at their first boundary. A pending
93 retains its written iterator and SAME source phase rather than resetting it. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : SourceState) :
    advance C K (PV_LIB_A_SpawnEnter12.enter270Programs P) resources encode H values
      (steps C H q) q = after C H q := by
  let T := PV_LIB_A_SpawnEnter12.enter270Programs P
  have spawn (q : State) : advance C K T resources encode H values
      (PV_THR2_Source15SpawnEnter.steps C q) ⟨q,none⟩ =
      ⟨PV_THR2_Source15SpawnEnter.after C q,none⟩ :=
    PV_LIB_A_SpawnEnter12.spawn C K (PV_THR2_Source270Table.resolve P) resources encode H values q
  unfold steps after spawnAfter aggregateAfter liftedSteps liftedAfter
  rw [advance_add,advance_add]
  rw [PV_LIB_A_SourceContinuation12.run C K T resources encode H values _ _
    (PV_LIB_A_ClosureAggregate12.run C K T resources encode H values)]
  rw [PV_LIB_A_SourceContinuation12.run C K T resources encode H values _ _ spawn]
  exact PV_LIB_A_SourceContinuation12.run C K T resources encode H values _ _
    (PV_LIB_A_F166History12.run C K P resources encode H values) _

/-- This explicit phase theorem prevents a later segment from re-polling93
as a fresh operation. No world/event/store component is discarded. -/
theorem retained (C : Carrier OWNER Data) (H : Handler) (q : State)
    (site : SourceSite) (tail : PV_LIB_A_WeakDropSource.Tail) :
    steps C H ⟨q,some (site,tail)⟩ = 0 ∧ after C H ⟨q,some (site,tail)⟩ = ⟨q,some (site,tail)⟩ := by
  constructor <;> rfl

#print axioms aggregateAfter
#print axioms spawnAfter
#print axioms steps
#print axioms after
#print axioms run
#print axioms retained
end PV_LIB_A_Post93Prefix12
