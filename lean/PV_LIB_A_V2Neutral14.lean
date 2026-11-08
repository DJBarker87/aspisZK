import PV_LIB_A_PrefixMachine11
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_V2Neutral14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary PV_LIB_StoreActionTable

theorem table_none (fn : Data) (none : v2Source fn = Option.none) : v2 fn = Option.none := by
  unfold v2Source at none
  split at none <;> simp_all

/-- The successor table retains every old v2 writer. Neutrality of the larger
selector therefore proves neutrality of the retained selector, not adequacy of
any missing native or wrapper semantics. -/
theorem select_none (P : Data → Option PV_STX2_SliceSyntax.Program) (c : Config)
    (none : sourceSelect P c = Option.none) : select P c = Option.none := by
  cases done : c.frame.completed with
  | some r => simp [select,done]
  | none =>
    cases waiting : c.frame.waiting with
    | none => simp [select,done,waiting]
    | some wait =>
      cases request : wait.request with
      | copy x y z => simp [select,done,waiting,request]
      | drop fn x => simp [select,done,waiting,request]
      | child fn a args =>
        cases resolved : P fn with
        | some body => simp [select,done,waiting,request,resolved]
        | none =>
          cases action : v2Source fn with
          | some meaning => simp [sourceSelect,done,waiting,request,resolved,action] at none
          | none => simp [select,done,waiting,request,resolved,table_none fn action]

theorem neutral (P : Data → Option PV_STX2_SliceSyntax.Program) (s : State)
    (none : SourceNeutral P s) : Neutral P s := by
  intro c hc
  exact select_none P c (none c hc)

/-- Exact step transport to original v2 away from successor source actions.
The SOURCE phase must be absent. Both sides retain the SAME OWNER layer,
resource replies, registry, source cells, native answers and ordered events. -/
theorem successor_step (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : State)
    (none : SourceNeutral P s) :
    PV_LIB_A_DeferredActions.step C K P resources encode H values ⟨s,Option.none⟩ =
      ⟨PV_LIB_StoreActionTable.step C K P resources encode H values s,Option.none⟩ := by
  rw [PV_LIB_A_DeferredActions.agreement C K P resources encode H values s none,
    PV_LIB_StoreActionTable.agreement C K P resources encode H values s (neutral P s none)]

#print axioms table_none
#print axioms select_none
#print axioms neutral
#print axioms successor_step
end PV_LIB_A_V2Neutral14
