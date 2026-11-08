import PV_LIB_A_F6CatchHistory13
import PV_LIB_A_F219Issue31813
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F6IssuedHistory13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11
abbrev programs := PV_THR2_CatchChildren.table

def steps (C : Carrier OWNER Data) (H : Handler) (q : SourceState) :=
  PV_LIB_A_F6CatchHistory13.steps C H q +
    PV_LIB_A_SourceContinuation12.steps (PV_LIB_A_F219Issue31813.steps C)
      (PV_LIB_A_F6CatchHistory13.stage7 C H q)

def after (C : Carrier OWNER Data) (H : Handler) (q : SourceState) :=
  PV_LIB_A_SourceContinuation12.after (PV_LIB_A_F219Issue31813.after C)
    (PV_LIB_A_F6CatchHistory13.stage7 C H q)

/-- Post124 through the ACTUAL issued9196 request, with no supplied callback
address, frame, payload or readback. All previous native and source stops survive. -/
theorem continuation (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : SourceState) :
    PV_LIB_A_PrefixMachine11.advance C K (programs P) resources encode H values (steps C H q) q = after C H q := by
  unfold steps after
  rw [advance_add,PV_LIB_A_F6CatchHistory13.continuation C K P resources encode H values q]
  exact PV_LIB_A_SourceContinuation12.run C K (programs P) resources encode H values _ _
    (PV_LIB_A_F219Issue31813.run C K P resources encode H values) _

/-- Same f6 BODY-entry source machine through actual125/219/134 and9196
issuance. Callback selection/entry is the next correspondence, not assumed by
this equality. This does not establish a full f6 Post or original-entry14756 run. -/
theorem history (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : Store Data) (a : Nat)
    (parents : List Frame) (b : Bool) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    let t := PV_THR2_ScopePrologue.prepared s a
    let r := PV_THR2_ScopeReply121.reply H t w
    let B := PV_LIB_A_F6Counter11.carrier C b
    let q := PV_LIB_A_F6EarlyHistory11.after B H t a parents r es stack
    let u := PV_LIB_A_F6History12.after B H q
    PV_LIB_A_PrefixMachine11.advance B K (programs P) resources encode H values
      (((18 + PV_LIB_A_F6EarlyHistory11.steps H t a r) + PV_LIB_A_F6History12.steps B q) + steps B H u)
      ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body},parents,s⟩,w,es⟩,stack⟩,none⟩ = after B H u := by
  intro t r B q u
  have first := PV_LIB_A_F6History12.history C K
    (PV_THR2_ScopeWrappers.resolve (PV_THR2_CatchChildren.resolve P)) resources encode H values s a parents b w es stack
  change PV_LIB_A_PrefixMachine11.advance B K (programs P) resources encode H values
    ((18 + PV_LIB_A_F6EarlyHistory11.steps H t a r) + PV_LIB_A_F6History12.steps B q) _ = u at first
  rw [advance_add,first]
  exact continuation B K P resources encode H values u

#print axioms steps
#print axioms after
#print axioms continuation
#print axioms history
end PV_LIB_A_F6IssuedHistory13
