import PV_LIB_A_F6Captures13
import PV_LIB_A_F6Enter12513
import PV_LIB_A_F125Prologue13
import PV_LIB_A_F125Enter21913
import PV_LIB_A_F219Prologue13
import PV_LIB_A_F219Full13413
import PV_LIB_A_F219To31813
import PV_LIB_A_SourceContinuation12
import PV_LIB_A_F6History12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F6CatchHistory13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11
abbrev liftSteps := PV_LIB_A_SourceContinuation12.steps
abbrev liftAfter := PV_LIB_A_SourceContinuation12.after
abbrev programs := PV_THR2_CatchChildren.table

def stage1 (C : Carrier OWNER Data) (H : Handler) (q : SourceState) :=
  liftAfter (PV_LIB_A_F6Captures13.after C ) q

def stage2 (C : Carrier OWNER Data) (H : Handler) (q : SourceState) :=
  liftAfter (PV_LIB_A_F6Enter12513.after C ) (stage1 C H q)

def stage3 (C : Carrier OWNER Data) (H : Handler) (q : SourceState) :=
  liftAfter (PV_LIB_A_F125Prologue13.after C ) (stage2 C H q)

def stage4 (C : Carrier OWNER Data) (H : Handler) (q : SourceState) :=
  liftAfter (PV_LIB_A_F125Enter21913.after C ) (stage3 C H q)

def stage5 (C : Carrier OWNER Data) (H : Handler) (q : SourceState) :=
  liftAfter (PV_LIB_A_F219Prologue13.after C ) (stage4 C H q)

def stage6 (C : Carrier OWNER Data) (H : Handler) (q : SourceState) :=
  liftAfter (PV_LIB_A_F219Full13413.after C H) (stage5 C H q)

def stage7 (C : Carrier OWNER Data) (H : Handler) (q : SourceState) :=
  liftAfter (PV_LIB_A_F219To31813.after C ) (stage6 C H q)

def steps (C : Carrier OWNER Data) (H : Handler) (q : SourceState) :=
  liftSteps (PV_LIB_A_F6Captures13.steps C) q +
  liftSteps (PV_LIB_A_F6Enter12513.steps C) (stage1 C H q) +
  liftSteps (PV_LIB_A_F125Prologue13.steps C) (stage2 C H q) +
  liftSteps (PV_LIB_A_F125Enter21913.steps C) (stage3 C H q) +
  liftSteps (PV_LIB_A_F219Prologue13.steps C) (stage4 C H q) +
  liftSteps (PV_LIB_A_F219Full13413.steps C) (stage5 C H q) +
  liftSteps (PV_LIB_A_F219To31813.steps C) (stage6 C H q)

/-- Continuous actual f6 post124-to9196 source frontier, including125/219 and
FULL134. Every earlier stop and retained source phase remains at its own frontier.
This stops before318 invocation; it is not the callback-to3400 or a full f6 Post. -/
theorem continuation (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : SourceState) :
    PV_LIB_A_PrefixMachine11.advance C K (programs P) resources encode H values (steps C H q) q = stage7 C H q := by
  have h1 := PV_LIB_A_SourceContinuation12.run C K (programs P) resources encode H values
    (PV_LIB_A_F6Captures13.steps C) (PV_LIB_A_F6Captures13.after C )
    (PV_LIB_A_F6Captures13.run C K (programs P) resources encode H values) q
  change _ = stage1 C H q at h1
  have h2 := PV_LIB_A_SourceContinuation12.run C K (programs P) resources encode H values
    (PV_LIB_A_F6Enter12513.steps C) (PV_LIB_A_F6Enter12513.after C )
    (PV_LIB_A_F6Enter12513.run C K P resources encode H values) (stage1 C H q)
  change _ = stage2 C H q at h2
  have h3 := PV_LIB_A_SourceContinuation12.run C K (programs P) resources encode H values
    (PV_LIB_A_F125Prologue13.steps C) (PV_LIB_A_F125Prologue13.after C )
    (PV_LIB_A_F125Prologue13.run C K (programs P) resources encode H values) (stage2 C H q)
  change _ = stage3 C H q at h3
  have h4 := PV_LIB_A_SourceContinuation12.run C K (programs P) resources encode H values
    (PV_LIB_A_F125Enter21913.steps C) (PV_LIB_A_F125Enter21913.after C )
    (PV_LIB_A_F125Enter21913.run C K P resources encode H values) (stage3 C H q)
  change _ = stage4 C H q at h4
  have h5 := PV_LIB_A_SourceContinuation12.run C K (programs P) resources encode H values
    (PV_LIB_A_F219Prologue13.steps C) (PV_LIB_A_F219Prologue13.after C )
    (PV_LIB_A_F219Prologue13.run C K (programs P) resources encode H values) (stage4 C H q)
  change _ = stage5 C H q at h5
  have h6 := PV_LIB_A_SourceContinuation12.run C K (programs P) resources encode H values
    (PV_LIB_A_F219Full13413.steps C) (PV_LIB_A_F219Full13413.after C H)
    (PV_LIB_A_F219Full13413.run C K P resources encode H values) (stage5 C H q)
  change _ = stage6 C H q at h6
  have h7 := PV_LIB_A_SourceContinuation12.run C K (programs P) resources encode H values
    (PV_LIB_A_F219To31813.steps C) (PV_LIB_A_F219To31813.after C )
    (PV_LIB_A_F219To31813.run C K (programs P) resources encode H values) (stage6 C H q)
  change _ = stage7 C H q at h7
  unfold steps
  rw [advance_add, advance_add, advance_add, advance_add, advance_add, advance_add]
  change PV_LIB_A_PrefixMachine11.advance C K (programs P) resources encode H values _
    (PV_LIB_A_PrefixMachine11.advance C K (programs P) resources encode H values _ _) = _
  rw [h1]
  change PV_LIB_A_PrefixMachine11.advance C K (programs P) resources encode H values _
    (PV_LIB_A_PrefixMachine11.advance C K (programs P) resources encode H values _ _) = _
  rw [h2]
  change PV_LIB_A_PrefixMachine11.advance C K (programs P) resources encode H values _
    (PV_LIB_A_PrefixMachine11.advance C K (programs P) resources encode H values _ _) = _
  rw [h3]
  change PV_LIB_A_PrefixMachine11.advance C K (programs P) resources encode H values _
    (PV_LIB_A_PrefixMachine11.advance C K (programs P) resources encode H values _ _) = _
  rw [h4]
  change PV_LIB_A_PrefixMachine11.advance C K (programs P) resources encode H values _
    (PV_LIB_A_PrefixMachine11.advance C K (programs P) resources encode H values _ _) = _
  rw [h5]
  change PV_LIB_A_PrefixMachine11.advance C K (programs P) resources encode H values _
    (PV_LIB_A_PrefixMachine11.advance C K (programs P) resources encode H values _ _) = _
  rw [h6]
  exact h7

/-- Continuous BODY-entry f6 history on the SAME corrected source machine and
program resolver through actual f125/219 and the pre318 frontier. It retains
native121/122/123/124/134 answers; their native representation laws remain separate. -/
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
      ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body},parents,s⟩,w,es⟩,stack⟩,none⟩ = stage7 B H u := by
  intro t r B q u
  have first := PV_LIB_A_F6History12.history C K
    (PV_THR2_ScopeWrappers.resolve (PV_THR2_CatchChildren.resolve P)) resources encode H values s a parents b w es stack
  change PV_LIB_A_PrefixMachine11.advance B K (programs P) resources encode H values
    ((18 + PV_LIB_A_F6EarlyHistory11.steps H t a r) + PV_LIB_A_F6History12.steps B q) _ = u at first
  rw [advance_add,first]
  exact continuation B K P resources encode H values u

#print axioms steps
#print axioms stage7
#print axioms continuation
#print axioms history
end PV_LIB_A_F6CatchHistory13
