import PV_LIB_A_F6CallbackHistory14
import PV_LIB_A_F316History13
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F6To220History14
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_LIB_StoreActionTable PV_THR2_SourceStoreLibrary PV_LIB_A_PrefixMachine11

def fallback (P : Data → Option PV_STX2_SliceSyntax.Program) :=
  PV_THR2_CatchPanicChild.resolve (PV_THR2_CatchTakeChild.resolve (PV_THR2_SourceTraitDispatch.resolve P))
def programs := PV_LIB_A_F316Enter22013.programs

def after (C : Carrier OWNER Data) (H : Handler) (q : SourceState) :=
  PV_LIB_A_F316History13.stage4 C H (PV_LIB_A_F6CallbackHistory14.stage7 C H q)
def steps (C : Carrier OWNER Data) (H : Handler) (q : SourceState) :=
  PV_LIB_A_F6CallbackHistory14.steps C H q +
  PV_LIB_A_F316History13.steps C H (PV_LIB_A_F6CallbackHistory14.stage7 C H q)

/-- One continuous source history, actual125/219/318/316/full410/220.
No selector, callback readback or successful410 value is supplied. -/
theorem continuation (base : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : SourceState) :
    let C := PV_THR2_EntryDynamic.carrier base b
    PV_LIB_A_PrefixMachine11.advance C K (programs P) resources encode H values (steps C H q) q = after C H q := by
  intro C
  have first := PV_LIB_A_F6CallbackHistory14.continuation base b K (fallback P) resources encode H values q
  change PV_LIB_A_PrefixMachine11.advance C K (programs P) resources encode H values _ q = _ at first
  unfold steps after
  rw [advance_add,first]
  exact PV_LIB_A_F316History13.run C K P resources encode H values _

/-- Same corrected-machine f6 BODY entry all the way to220 BODY entry or its
first earlier native/source stop, with the actual suspended219 parent. This
is prefix transport, not full f6 Post, native physical adequacy or OwnInit. -/
theorem history (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : Store Data) (a : Nat)
    (parents : List Frame) (b : Bool) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    let t := PV_THR2_ScopePrologue.prepared s a
    let r := PV_THR2_ScopeReply121.reply H t w
    let B := PV_LIB_A_F6Counter11.carrier C b
    let q := PV_LIB_A_F6EarlyHistory11.after B H t a parents r es stack
    let u := PV_LIB_A_F6History12.after B H q
    let v := PV_LIB_A_F6CallbackHistory14.stage7 B H u
    PV_LIB_A_PrefixMachine11.advance B K (programs P) resources encode H values
      ((((18 + PV_LIB_A_F6EarlyHistory11.steps H t a r) + PV_LIB_A_F6History12.steps B q) +
        PV_LIB_A_F6CallbackHistory14.steps B H u) + PV_LIB_A_F316History13.steps B H v)
      ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body},parents,s⟩,w,es⟩,stack⟩,none⟩ =
      PV_LIB_A_F316History13.stage4 B H v := by
  intro t r B q u v
  have first := PV_LIB_A_F6CallbackHistory14.history C K (fallback P) resources encode H values s a parents b w es stack
  change PV_LIB_A_PrefixMachine11.advance B K (programs P) resources encode H values _ _ = v at first
  rw [advance_add,first]
  exact PV_LIB_A_F316History13.run B K P resources encode H values v

#print axioms fallback
#print axioms continuation
#print axioms history
end PV_LIB_A_F6To220History14
