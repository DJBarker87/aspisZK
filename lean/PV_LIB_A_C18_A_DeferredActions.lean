import PV_LIB_A_StoreActionTable7
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_DeferredActions
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable

/-- These four named meanings perform NO source write on pending. Their write
is selected by the eventual full answer; it must not be skipped on retry. -/
inductive Deferred where
  | vecPush167 | vecAppend10 | weakCas530 | strongCas555

def action : Deferred → SourceAction
  | .vecPush167 => .inherited (.legacy .vecPush167)
  | .vecAppend10 => .inherited (.legacy .vecAppend10)
  | .weakCas530 => .inherited (.primitive .cas530)
  | .strongCas555 => .inherited (.primitive .cas555)

def deferred : SourceAction → Option Deferred
  | .inherited (.legacy .vecPush167) => some .vecPush167
  | .inherited (.legacy .vecAppend10) => some .vecAppend10
  | .inherited (.primitive .cas530) => some .weakCas530
  | .inherited (.primitive .cas555) => some .strongCas555
  | _ => none

theorem classified (d : Deferred) : deferred (action d) = some d := by
  cases d <;> rfl

/-- Checked on the exact documented functions, on ALL argument/source shapes.
This is why re-evaluation on a retry cannot duplicate an already-applied write.
No successful-answer or source-write premise enters any row's interface. -/
theorem pending_start (C : Carrier OWNER Data) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (d : Deferred) (fn : Data) (args : List Data) (s : Store Data) (w post : OWNER)
    (events : List PV_RJ4IDB.NativeEvent) :
    start C values (action d) fn args s w ⟨.pending,post,events⟩ = some ⟨s,.done⟩ := by
  cases d <;> rfl

/-- Refine the intermediate polling model only at a retained deferred phase.
Already-applied prefixes and last-Weak deallocation retain Table7's staging. -/
def step (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : SourceState) : SourceState :=
  match s.applied with
  | some (site,.done) => match deferred site.action with
    | some _ => match s.base.current.status with
      | .running c => sourceBegin C values c s.base.current.world s.base.current.events
          s.base.suspended site (H site.waiting.request s.base.current.world)
      | _ => sourceStep C K P resources encode H values s
    | none => sourceStep C K P resources encode H values s
  | _ => sourceStep C K P resources encode H values s

/-- Every eventual reply executes the SAME fixed named operation, including
CAS failure/spurious failure, allocation failure, faults and divergence. -/
theorem deferred_retry (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : SourceSite) (d : Deferred) (selected : site.action = action d) :
    step C K P resources encode H values ⟨⟨⟨.running c,w,es⟩,stack⟩,some (site,.done)⟩ =
      sourceBegin C values c w es stack site (H site.waiting.request w) := by
  simp only [step,selected,classified]

/-- A repeated pending deferred answer has no write, and retains exactly the
request/config/world/event suffix needed to apply a later completion once. -/
theorem deferred_pending (C : Carrier OWNER Data) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w post : OWNER) (es events : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : SourceSite) (d : Deferred) (selected : site.action = action d) :
    sourceBegin C values c w es stack site ⟨.pending,post,events⟩ =
      ⟨⟨⟨.running c,post,es ++ events⟩,stack⟩,some (site,.done)⟩ := by
  unfold sourceBegin
  rw [selected,pending_start]
  exact source_pending C c es events stack site .done post

/-- The symbolic agreement remains against the exact OWNER-aware interpreter,
with its original resource environment and no retained source phase. -/
theorem agreement (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : State)
    (away : SourceNeutral P s) :
    step C K P resources encode H values ⟨s,none⟩ =
      ⟨PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H s,none⟩ :=
  source_agreement C K P resources encode H values s away

#print axioms action
#print axioms deferred
#print axioms classified
#print axioms pending_start
#print axioms step
#print axioms deferred_retry
#print axioms deferred_pending
#print axioms agreement
end PV_LIB_A_DeferredActions
