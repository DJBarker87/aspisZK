import PV_LIB_A_F6Arc12
import PV_LIB_A_SourceContinuation12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F6History12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11
abbrev liftedSteps := PV_LIB_A_SourceContinuation12.steps
abbrev liftedAfter := PV_LIB_A_SourceContinuation12.after

def afterData (C : Carrier OWNER Data) (q : SourceState) := liftedAfter (PV_LIB_A_F6Data12.after C) q

def afterStorage (C : Carrier OWNER Data) (q : SourceState) :=
  liftedAfter (PV_LIB_A_F6Arc12.storageAfter C) (afterData C q)

def steps (C : Carrier OWNER Data) (q : SourceState) :=
  liftedSteps PV_LIB_A_F6Data12.steps q +
  liftedSteps (PV_LIB_A_F6Arc12.storageSteps C) (afterData C q) +
  liftedSteps (PV_LIB_A_F6Arc12.steps C) (afterStorage C q)

def after (C : Carrier OWNER Data) (H : Handler) (q : SourceState) :=
  liftedAfter (PV_LIB_A_F6Arc12.after C H) (afterStorage C q)

/-- Actual1876 ScopeData, source cleanup of moved temporaries and full1916
Arc124 boundary. All earlier source/native stops remain at their own frontier. -/
theorem continuation (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : SourceState) :
    advance C K (PV_THR2_ScopeChildren.table P) resources encode H values (steps C q) q = after C H q := by
  let T := PV_THR2_ScopeChildren.table P
  unfold steps after afterStorage afterData liftedSteps liftedAfter
  rw [advance_add,advance_add]
  rw [PV_LIB_A_SourceContinuation12.run C K T resources encode H values _ _
    (PV_LIB_A_F6Data12.run C K T resources encode H values)]
  rw [PV_LIB_A_SourceContinuation12.run C K T resources encode H values _ _
    (PV_LIB_A_F6Arc12.storage C K T resources encode H values)]
  exact PV_LIB_A_SourceContinuation12.run C K T resources encode H values _ _
    (PV_LIB_A_F6Arc12.run C K P resources encode H values) _

/-- Continuous corrected f6 BODY-entry history through FULL124, or first
121/122/123/source/124 stop. Native values and physical constructor binding
remain separate obligations. No full f6 Post or connection to3400 is claimed. -/
theorem history (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : Store Data) (a : Nat)
    (parents : List Frame) (b : Bool) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    let t := PV_THR2_ScopePrologue.prepared s a
    let r := PV_THR2_ScopeReply121.reply H t w
    let B := PV_LIB_A_F6Counter11.carrier C b
    let q := PV_LIB_A_F6EarlyHistory11.after B H t a parents r es stack
    advance B K (PV_THR2_ScopeChildren.table P) resources encode H values
      ((18 + PV_LIB_A_F6EarlyHistory11.steps H t a r) + steps B q)
      ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body},parents,s⟩,w,es⟩,stack⟩,none⟩ = after B H q := by
  intro t r B q
  rw [advance_add,PV_LIB_A_F6EarlyHistory11.history C K P resources encode H values s a parents b w es stack]
  exact continuation B K P resources encode H values q

#print axioms afterData
#print axioms afterStorage
#print axioms steps
#print axioms after
#print axioms continuation
#print axioms history
end PV_LIB_A_F6History12
