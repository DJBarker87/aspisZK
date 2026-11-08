import PV_LIB_A_F6SourceSequences14
import PV_LIB_A_PrefixStructuredCalls14
import PV_LIB_A_F125Prologue13
import PV_LIB_A_F219Prologue13
import PV_LIB_A_PrefixNativeCalls14
import PV_LIB_A_F219CallbackHistory14
import PV_LIB_A_V2Callback14
import PV_LIB_A_F316Prefix13
import PV_LIB_A_F316ToInvoke13
import PV_LIB_A_F220Prefix14
import PV_LIB_A_F208Prefix14
import PV_LIB_A_V2ActualBindings14
import PV_LIB_A_V2Composition14
import PV_LIB_A_Full124TableGap14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_V2Post124To15
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary PV_LIB_StoreActionTable
open PV_LIB_A_V2Composition14 PV_LIB_A_StructuredFrontier13

/-- Exact post124 source table fragment, COMPATIBLE with the Full BODY table.
In particular this asks for NO native124 reply. -/
structure Lookups (P : Data → Option PV_STX2_SliceSyntax.Program) : Prop where
  native134 : P (fn PV_LIB_A_PrefixNativeCalls14.src134) = none
  native410 : P (fn PV_LIB_A_PrefixNativeCalls14.src410) = none
  body125 : P (fn PV_LIB_A_PrefixStructuredCalls14.src125) = some PV_THR2_F125.live
  body219 : P (fn PV_LIB_A_PrefixStructuredCalls14.src219) = some PV_THR2_F219.live
  body220 : P (fn PV_LIB_A_PrefixStructuredCalls14.src220) = some PV_THR2_F220.live
  body208 : P (fn PV_LIB_A_PrefixStructuredCalls14.src208) = some PV_THR2_F208.live
  body15 : P (fn PV_LIB_A_PrefixStructuredCalls14.src15) = some PV_THR2_F15.live

def segments (C : Carrier OWNER Data) (H : Handler) : List Segment :=
  [
    ⟨PV_LIB_A_F6SourceSequences14.stepsE C,PV_LIB_A_F6SourceSequences14.afterE C⟩,
    ⟨PV_LIB_A_PrefixStructuredCalls14.steps125 C,PV_LIB_A_PrefixStructuredCalls14.after125 C⟩,
    ⟨PV_LIB_A_F125Prologue13.steps C,PV_LIB_A_F125Prologue13.after C⟩,
    ⟨PV_LIB_A_PrefixStructuredCalls14.steps219 C,PV_LIB_A_PrefixStructuredCalls14.after219 C⟩,
    ⟨PV_LIB_A_F219Prologue13.steps C,PV_LIB_A_F219Prologue13.after C⟩,
    ⟨PV_LIB_A_PrefixNativeCalls14.steps134 C,PV_LIB_A_PrefixNativeCalls14.after134 C H⟩,
    ⟨PV_LIB_A_F219CallbackHistory14.cost1 C,PV_LIB_A_F219CallbackHistory14.finish1 C⟩,
    ⟨PV_LIB_A_V2Callback14.steps,PV_LIB_A_V2Callback14.after⟩,
    ⟨PV_LIB_A_F316Prefix13.steps C,PV_LIB_A_F316Prefix13.after C⟩,
    ⟨PV_LIB_A_PrefixNativeCalls14.steps410 C,PV_LIB_A_PrefixNativeCalls14.after410 C H⟩,
    ⟨PV_LIB_A_F316ToInvoke13.steps C,PV_LIB_A_F316ToInvoke13.after C⟩,
    ⟨PV_LIB_A_PrefixStructuredCalls14.steps220 C,PV_LIB_A_PrefixStructuredCalls14.after220 C⟩,
    ⟨PV_LIB_A_F220Prefix14.steps C,PV_LIB_A_F220Prefix14.after C⟩,
    ⟨PV_LIB_A_PrefixStructuredCalls14.steps208 C,PV_LIB_A_PrefixStructuredCalls14.after208 C⟩,
    ⟨PV_LIB_A_F208Prefix14.steps C,PV_LIB_A_F208Prefix14.after C⟩,
    ⟨PV_LIB_A_PrefixStructuredCalls14.steps15 C,PV_LIB_A_PrefixStructuredCalls14.after15 C⟩
  ]
def route (C : Carrier OWNER Data) (H : Handler) := chain (segments C H)

/-- ORIGINAL v2 post124 caller continuation through the actual callback chain
into15, or the first earlier source/native stop. All native FULL contracts and
source helpers are applied BY NAME. CLOSED124's actual Post store must first
be transported into this continuation; no opaque124 surrogate is used here. -/
theorem certified (base : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (lookups : Lookups P)
    (resources : Resources) (encode : Encode) (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) :
    let C := PV_THR2_EntryDynamic.carrier base b
    Certified C K P resources encode H values (route C H) := by
  intro C
  apply chained
  intro x hx
  simp [segments] at hx
  rcases hx with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
  · subst x
    exact PV_LIB_A_V2Frontiers14.sequence C K P resources encode H values PV_LIB_A_F6SourceSequences14.seqE _ PV_LIB_A_F6SourceSequences14.offE
  · subst x
    exact PV_LIB_A_V2ActualBindings14.run125 C K P lookups.body125 resources encode H values
  · subst x
    exact PV_LIB_A_V2Frontiers14.sequence C K P resources encode H values PV_LIB_A_F125Prologue13.seq _ PV_LIB_A_F125Prologue13.off
  · subst x
    exact PV_LIB_A_V2ActualBindings14.run219 C K P lookups.body219 resources encode H values
  · subst x
    exact PV_LIB_A_V2Frontiers14.sequence C K P resources encode H values PV_LIB_A_F219Prologue13.seq _ PV_LIB_A_F219Prologue13.off
  · subst x
    exact PV_LIB_A_V2ActualBindings14.run134 C K P lookups.native134 resources encode H values
  · subst x
    exact PV_LIB_A_V2Frontiers14.sequence C K P resources encode H values PV_LIB_A_F219CallbackHistory14.seq _ PV_LIB_A_F219CallbackHistory14.off
  · subst x
    exact PV_LIB_A_V2Callback14.run base b K P resources encode H values
  · subst x
    exact PV_LIB_A_V2Frontiers14.sequence C K P resources encode H values PV_LIB_A_F316Prefix13.seq _ PV_LIB_A_F316Prefix13.off
  · subst x
    exact PV_LIB_A_V2ActualBindings14.run410 C K P lookups.native410 resources encode H values
  · subst x
    exact PV_LIB_A_V2Frontiers14.sequence C K P resources encode H values PV_LIB_A_F316ToInvoke13.seq _ PV_LIB_A_F316ToInvoke13.off
  · subst x
    exact PV_LIB_A_V2ActualBindings14.run220 C K P lookups.body220 resources encode H values
  · subst x
    exact PV_LIB_A_V2Frontiers14.sequence C K P resources encode H values PV_LIB_A_F220Prefix14.seq _ PV_LIB_A_F220Prefix14.off
  · subst x
    exact PV_LIB_A_V2ActualBindings14.run208 C K P lookups.body208 resources encode H values
  · subst x
    exact PV_LIB_A_V2Frontiers14.sequence C K P resources encode H values PV_LIB_A_F208Prefix14.seq _ PV_LIB_A_F208Prefix14.off
  · subst x
    exact PV_LIB_A_V2ActualBindings14.run15 C K P lookups.body15 resources encode H values

/-- Applied to a whole post124 source configuration, retaining exact worlds,
events, stores and callers. This is not original Entry14 reachability, complete
LoopInvariant initialization/preservation, or the14756 OwnInit witness. -/
theorem history (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (lookups : Lookups P)
    (resources : Resources) (encode : Encode) (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (q : State) :
    let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
    PV_LIB_StoreActionTable.advance B K P resources encode H values ((route B H).steps q) q = (route B H).after q :=
  certified (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier C)))
    b K P lookups resources encode H values q

#print axioms segments
#print axioms route
#print axioms certified
#print axioms history
end PV_LIB_A_V2Post124To15
