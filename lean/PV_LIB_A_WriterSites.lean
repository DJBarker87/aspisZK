import PV_LIB_A_OwnerStore
import PV_W1_LeafBoundary
import PV_THR2_F1
import PV_THR2_F15
import PV_THR2_F207
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_WriterSites
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_W1_LeafBoundary
open PV_LIB_A_OwnerStore PV_THR2_SourceStoreLibrary
/-- Read the actual emitted token, preserving all generic metadata. -/
def callee : PV_STX2_SliceSyntax.Node → Data
  | .leaf (.call _ fn _ _ _) => fn
  | _ => .null
/-- Check the exact writer inventory and moved source operands. This is not a
claim that an arbitrary run reaches these instructions. -/
def signature : PV_STX2_SliceSyntax.Node → Option
    (PV_THR2_SourceStoreNative.Function × List Operand × PV_STX2_Syntax.Place)
  | .leaf (.call _ fn args dest _) => do
      let f ← PV_THR2_SourceStoreNative.function fn
      pure (f,args,dest)
  | _ => none

theorem source487 : signature PV_THR2_F1.node88 =
    some (.intoIterNext9,[.move (.local 28)],.local 27) := rfl
theorem source930 : signature PV_THR2_F1.node125 =
    some (.vecAppend10,[.move (.local 32),.move (.local 33)],.local 26) := rfl
theorem source3447 : signature PV_THR2_F15.node17 =
    some (.rangeNext93,[.move (.local 9)],.local 8) := rfl
theorem source3519 : signature PV_THR2_F15.node38 =
    some (.vecPush167,[.move (.local 14),.move (.local 15)],.local 13) := rfl
theorem source3641 : signature PV_THR2_F15.node68 =
    some (.vecPush167,[.move (.local 23),.move (.local 24)],.local 22) := rfl
theorem source3756 : signature PV_THR2_F15.node84 =
    some (.intoIterNext9,[.move (.local 29)],.local 28) := rfl
theorem source4327 : signature PV_THR2_F15.node122 =
    some (.vecPush167,[.move (.local 33),.move (.local 34)],.local 32) := rfl


def boolTrue : Data := .object [("kind",.object [("Literal",.object [("Bool",.boolean true)])]),
  ("ty",.object [("Deduplicated",.number 556)])]
theorem source8248 : signature PV_THR2_F207.node5 =
    some (.cellReplace289,[.move (.local 4),.constant boolTrue],.local 0) := rfl

/-- The site is built from the actual issued request, not a separate alias,
receiver or supplied store delta. -/
def site (e : Entry) (f : PV_THR2_SourceStoreNative.Function) : PV_THR2_SourceStoreNative.Site :=
  ⟨f,e.callee,PV_THR2_StaticReply.wait e.store e.callee e.arguments e.destination,
    e.arguments⟩

theorem selected (P : Data → Option PV_STX2_SliceSyntax.Program) (e : Entry)
    (f : PV_THR2_SourceStoreNative.Function) (leaf : P e.callee = none)
    (meaning : PV_THR2_SourceStoreNative.function e.callee = some f) :
    PV_THR2_SourceStoreNative.select P (pending e) = some (site e f) := by
  change (match P e.callee with
    | some _ => none
    | none => (PV_THR2_SourceStoreNative.function e.callee).bind
        (fun k => some (site e k))) = some (site e f)
  rw [leaf,meaning]
  rfl

/-- Every writer graph is bound to the corrected OWNER PV_LIB_A_OwnerStore.step at the issued poll.
Values are still explicit runtime values; this theorem does not invent them. -/
theorem installed (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (e : Entry) (f : PV_THR2_SourceStoreNative.Function) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (leaf : P e.callee = none)
    (meaning : PV_THR2_SourceStoreNative.function e.callee = some f)
    (ordinary : PV_THR2_Catch316Segment.select (pending e) = none) :
    PV_LIB_A_SourceWriters.law C values (pending e) w es e.suspended (site e f)
      (H (site e f).waiting.request w)
      (PV_LIB.observe (PV_LIB_A_OwnerStore.step C K P resources encode H values
        ⟨⟨.running (pending e),w,es⟩,e.suspended⟩)) :=
  PV_LIB_A_OwnerStore.installed C K P resources encode H values (pending e) w es
    e.suspended (site e f) ordinary (selected P e f leaf meaning)
#print axioms source487
#print axioms source930
#print axioms source3447
#print axioms source3519
#print axioms source3641
#print axioms source3756
#print axioms source4327
#print axioms source8248
#print axioms selected
#print axioms installed
end PV_LIB_A_WriterSites
