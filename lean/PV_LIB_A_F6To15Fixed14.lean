import PV_LIB_A_F6SourceSequences14
import PV_LIB_A_PrefixNativeCalls14
import PV_LIB_A_PrefixStructuredCalls14
import PV_LIB_A_F125Prologue13
import PV_LIB_A_F219Prologue13
import PV_LIB_A_F219CallbackHistory14
import PV_LIB_A_F219Enter316Any14
import PV_LIB_A_F316Prefix13
import PV_LIB_A_F316ToInvoke13
import PV_LIB_A_F220Prefix14
import PV_LIB_A_F208Prefix14
import PV_LIB_A_PrefixComposition14
import PV_LIB_A_F6Counter11
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F6To15Fixed14
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_LIB_StoreActionTable PV_THR2_SourceStoreLibrary PV_LIB_A_PrefixMachine11
open PV_LIB_A_PrefixComposition14
abbrev programs := PV_LIB_A_SpawnEnter12.enter270Programs

def segments (C : Carrier OWNER Data) (H : Handler) : List Segment :=
  [
    lift (PV_LIB_A_F6SourceSequences14.stepsA C) (PV_LIB_A_F6SourceSequences14.afterA C),
    lift (PV_LIB_A_PrefixNativeCalls14.steps121 C) (PV_LIB_A_PrefixNativeCalls14.after121 C H),
    lift (PV_LIB_A_F6SourceSequences14.stepsB C) (PV_LIB_A_F6SourceSequences14.afterB C),
    lift (PV_LIB_A_PrefixNativeCalls14.steps122 C) (PV_LIB_A_PrefixNativeCalls14.after122 C H),
    lift (PV_LIB_A_F6SourceSequences14.stepsC C) (PV_LIB_A_F6SourceSequences14.afterC C),
    lift (PV_LIB_A_PrefixNativeCalls14.steps123 C) (PV_LIB_A_PrefixNativeCalls14.after123 C H),
    lift (PV_LIB_A_F6SourceSequences14.stepsD C) (PV_LIB_A_F6SourceSequences14.afterD C),
    lift (PV_LIB_A_PrefixNativeCalls14.steps124 C) (PV_LIB_A_PrefixNativeCalls14.after124 C H),
    lift (PV_LIB_A_F6SourceSequences14.stepsE C) (PV_LIB_A_F6SourceSequences14.afterE C),
    lift (PV_LIB_A_PrefixStructuredCalls14.steps125 C) (PV_LIB_A_PrefixStructuredCalls14.after125 C),
    lift (PV_LIB_A_F125Prologue13.steps C) (PV_LIB_A_F125Prologue13.after C),
    lift (PV_LIB_A_PrefixStructuredCalls14.steps219 C) (PV_LIB_A_PrefixStructuredCalls14.after219 C),
    lift (PV_LIB_A_F219Prologue13.steps C) (PV_LIB_A_F219Prologue13.after C),
    lift (PV_LIB_A_PrefixNativeCalls14.steps134 C) (PV_LIB_A_PrefixNativeCalls14.after134 C H),
    lift (PV_LIB_A_F219CallbackHistory14.cost1 C) (PV_LIB_A_F219CallbackHistory14.finish1 C),
    lift (PV_LIB_A_F219Enter316Any14.steps) (PV_LIB_A_F219Enter316Any14.after),
    lift (PV_LIB_A_F316Prefix13.steps C) (PV_LIB_A_F316Prefix13.after C),
    lift (PV_LIB_A_PrefixNativeCalls14.steps410 C) (PV_LIB_A_PrefixNativeCalls14.after410 C H),
    lift (PV_LIB_A_F316ToInvoke13.steps C) (PV_LIB_A_F316ToInvoke13.after C),
    lift (PV_LIB_A_PrefixStructuredCalls14.steps220 C) (PV_LIB_A_PrefixStructuredCalls14.after220 C),
    lift (PV_LIB_A_F220Prefix14.steps C) (PV_LIB_A_F220Prefix14.after C),
    lift (PV_LIB_A_PrefixStructuredCalls14.steps208 C) (PV_LIB_A_PrefixStructuredCalls14.after208 C),
    lift (PV_LIB_A_F208Prefix14.steps C) (PV_LIB_A_F208Prefix14.after C),
    lift (PV_LIB_A_PrefixStructuredCalls14.steps15 C) (PV_LIB_A_PrefixStructuredCalls14.after15 C)
  ]
def route (C : Carrier OWNER Data) (H : Handler) := chain (segments C H)

/-- SAME fixed resolver from f6 entry through actual125/219/318/316/220/208
and15 BODY entry. Every native answer and every source gap stays at its actual
frontier; callback tokens/address/selection come from emitted stores. This does
not assert full LoopInvariant, native adequacy, full f6 Post or original entry. -/
theorem certified (base : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) :
    let C := PV_THR2_EntryDynamic.carrier base b
    Certified C K (programs P) resources encode H values (route C H) := by
  intro C
  apply chained
  intro x hx
  simp [segments] at hx
  rcases hx with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23
  · subst x
    apply lifted
    exact PV_LIB_A_F6SourceSequences14.runA C K (programs P) resources encode H values
  · subst x
    apply lifted
    exact PV_LIB_A_PrefixNativeCalls14.run121 C K P resources encode H values
  · subst x
    apply lifted
    exact PV_LIB_A_F6SourceSequences14.runB C K (programs P) resources encode H values
  · subst x
    apply lifted
    exact PV_LIB_A_PrefixNativeCalls14.run122 C K P resources encode H values
  · subst x
    apply lifted
    exact PV_LIB_A_F6SourceSequences14.runC C K (programs P) resources encode H values
  · subst x
    apply lifted
    exact PV_LIB_A_PrefixNativeCalls14.run123 C K P resources encode H values
  · subst x
    apply lifted
    exact PV_LIB_A_F6SourceSequences14.runD C K (programs P) resources encode H values
  · subst x
    apply lifted
    exact PV_LIB_A_PrefixNativeCalls14.run124 C K P resources encode H values
  · subst x
    apply lifted
    exact PV_LIB_A_F6SourceSequences14.runE C K (programs P) resources encode H values
  · subst x
    apply lifted
    exact PV_LIB_A_PrefixStructuredCalls14.run125 C K P resources encode H values
  · subst x
    apply lifted
    exact PV_LIB_A_F125Prologue13.run C K (programs P) resources encode H values
  · subst x
    apply lifted
    exact PV_LIB_A_PrefixStructuredCalls14.run219 C K P resources encode H values
  · subst x
    apply lifted
    exact PV_LIB_A_F219Prologue13.run C K (programs P) resources encode H values
  · subst x
    apply lifted
    exact PV_LIB_A_PrefixNativeCalls14.run134 C K P resources encode H values
  · subst x
    apply lifted
    exact PV_LIB_A_SequenceFrontier13.run C K (programs P) resources encode H values
      PV_LIB_A_F219CallbackHistory14.seq _ PV_LIB_A_F219CallbackHistory14.off
  · subst x
    apply lifted
    exact PV_LIB_A_F219Enter316Any14.run base b K (programs P) resources encode H values
  · subst x
    apply lifted
    exact PV_LIB_A_F316Prefix13.run C K (programs P) resources encode H values
  · subst x
    apply lifted
    exact PV_LIB_A_PrefixNativeCalls14.run410 C K P resources encode H values
  · subst x
    apply lifted
    exact PV_LIB_A_F316ToInvoke13.run C K (programs P) resources encode H values
  · subst x
    apply lifted
    exact PV_LIB_A_PrefixStructuredCalls14.run220 C K P resources encode H values
  · subst x
    apply lifted
    exact PV_LIB_A_F220Prefix14.run C K (programs P) resources encode H values
  · subst x
    apply lifted
    exact PV_LIB_A_PrefixStructuredCalls14.run208 C K P resources encode H values
  · subst x
    apply lifted
    exact PV_LIB_A_F208Prefix14.run C K (programs P) resources encode H values
  · subst x
    apply lifted
    exact PV_LIB_A_PrefixStructuredCalls14.run15 C K P resources encode H values

/-- Whole BODY-entry equation, without a saved callback/decoder/native-success
premise. The resulting expression retains exact failure/pending source frontiers. -/
theorem history (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    let B := PV_LIB_A_F6Counter11.carrier C b
    let q : SourceState := ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body},parents,s⟩,w,es⟩,stack⟩,none⟩
    advance B K (programs P) resources encode H values ((route B H).steps q) q = (route B H).after q :=
  certified (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier C)) b K P resources encode H values _

#print axioms segments
#print axioms route
#print axioms certified
#print axioms history
end PV_LIB_A_F6To15Fixed14
