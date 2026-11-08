import PV_LIB_A_V2F124Entry14
import PV_LIB_A_F6SourceSequences14
import PV_LIB_A_V2Composition14
import PV_LIB_A_Full124TableGap14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_V2F6To12414
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary PV_LIB_StoreActionTable
open PV_LIB_A_V2Composition14 PV_LIB_A_StructuredFrontier13

/-- Actual full-table fragment BEFORE the first CLOSED BODY call. -/
structure Lookups (P : Data → Option PV_STX2_SliceSyntax.Program) : Prop where
  atomic121 : P (fn PV_LIB_A_PrefixNativeCalls14.src121) = none
  current122 : P (fn PV_LIB_A_PrefixNativeCalls14.src122) = none
  bool123 : P (fn PV_LIB_A_PrefixNativeCalls14.src123) = none
  body124 : P (fn PV_LIB_A_PrefixNativeCalls14.src124) = some PV_THR2_F124.live

/-- C's literal Full.body values 121/122/123/124 discharge these four fields
by rfl. No opaque124 or provider/native-handler replacement is requested. -/
theorem full_tables (bodies : Nat → Option PV_STX2_SliceSyntax.Program)
    (traits : Data → Option PV_STX2_SliceSyntax.Program)
    (atomic121 : bodies 121 = none) (current122 : bodies 122 = none)
    (bool123 : bodies 123 = none) (body124 : bodies 124 = some PV_THR2_F124.live) :
    Lookups (PV_LIB_A_Full124TableGap14.fullRegular bodies traits) :=
  ⟨atomic121,current122,bool123,body124⟩

def segments (C : Carrier OWNER Data) (H : Handler) : List Segment :=
  [⟨PV_LIB_A_F6SourceSequences14.stepsA C,PV_LIB_A_F6SourceSequences14.afterA C⟩,
   ⟨PV_LIB_A_PrefixNativeCalls14.steps121 C,PV_LIB_A_PrefixNativeCalls14.after121 C H⟩,
   ⟨PV_LIB_A_F6SourceSequences14.stepsB C,PV_LIB_A_F6SourceSequences14.afterB C⟩,
   ⟨PV_LIB_A_PrefixNativeCalls14.steps122 C,PV_LIB_A_PrefixNativeCalls14.after122 C H⟩,
   ⟨PV_LIB_A_F6SourceSequences14.stepsC C,PV_LIB_A_F6SourceSequences14.afterC C⟩,
   ⟨PV_LIB_A_PrefixNativeCalls14.steps123 C,PV_LIB_A_PrefixNativeCalls14.after123 C H⟩,
   ⟨PV_LIB_A_F6SourceSequences14.stepsD C,PV_LIB_A_F6SourceSequences14.afterD C⟩,
   ⟨PV_LIB_A_V2F124Entry14.steps C,PV_LIB_A_V2F124Entry14.after C⟩]
def route (C : Carrier OWNER Data) (H : Handler) := chain (segments C H)

/-- Actual v2 f6 prelude reaches124 BODY entry or its first earlier stop.
Named native FULL contracts and named source helpers are used; CLOSED124 is
NOT unfolded or replaced by a native reply. No readback/success input occurs. -/
theorem certified (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (lookups : Lookups P)
    (resources : Resources) (encode : Encode) (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) :
    Certified C K P resources encode H values (route C H) := by
  apply chained
  intro x hx
  simp [segments] at hx
  rcases hx with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst x; exact PV_LIB_A_V2Frontiers14.sequence C K P resources encode H values
      PV_LIB_A_F6SourceSequences14.seqA _ PV_LIB_A_F6SourceSequences14.offA
  · subst x; exact PV_LIB_A_V2ActualBindings14.run121 C K P lookups.atomic121 resources encode H values
  · subst x; exact PV_LIB_A_V2Frontiers14.sequence C K P resources encode H values
      PV_LIB_A_F6SourceSequences14.seqB _ PV_LIB_A_F6SourceSequences14.offB
  · subst x; exact PV_LIB_A_V2ActualBindings14.run122 C K P lookups.current122 resources encode H values
  · subst x; exact PV_LIB_A_V2Frontiers14.sequence C K P resources encode H values
      PV_LIB_A_F6SourceSequences14.seqC _ PV_LIB_A_F6SourceSequences14.offC
  · subst x; exact PV_LIB_A_V2ActualBindings14.run123 C K P lookups.bool123 resources encode H values
  · subst x; exact PV_LIB_A_V2Frontiers14.sequence C K P resources encode H values
      PV_LIB_A_F6SourceSequences14.seqD _ PV_LIB_A_F6SourceSequences14.offD
  · subst x; exact PV_LIB_A_V2F124Entry14.run C K P lookups.body124 resources encode H values

theorem history (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (lookups : Lookups P)
    (resources : Resources) (encode : Encode) (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    let q : State := ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body},parents,s⟩,w,es⟩,stack⟩
    PV_LIB_StoreActionTable.advance C K P resources encode H values ((route C H).steps q) q = (route C H).after q :=
  certified C K P lookups resources encode H values _

#print axioms full_tables
#print axioms segments
#print axioms route
#print axioms certified
#print axioms history
end PV_LIB_A_V2F6To12414
