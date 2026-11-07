import LIBB_C04LogGraph
import LIBB_C04InputPartition
set_option autoImplicit false
noncomputable section
namespace LIBB_C04RichTrace
open Aeneas Aeneas.Std AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open LIBB_C04LogGraph
/-- Every explicit native tree event retains its original physical partition,
even for rejected or truncated views; no tree-success premise is used. -/
theorem tree (kind : Usize) (events : List NLL.Event) :
 ∀ q ∈ NNC_C04Events.tree kind events, Canonical q := by
 intro q member
 obtain ⟨e,_,entered⟩ := List.mem_flatMap.mp member
 cases e with
 | entry lo n slot keys => cases entered
 | missingCount => cases entered
 | capacity nodes count => cases entered
 | padding nodes count => cases entered
 | leaf position key view digest =>
   have same : q = ⟨Port4B_LeafCode.input kind view,.ok digest⟩ := List.mem_singleton.mp entered
   subst q
   exact ⟨digest,rfl,LIBB_C04InputPartition.input kind view⟩
 | verify nodes count before queries out => exact LIBB_C04LogGraph.nodes queries q entered

theorem shapes {H : Bytes → State} {proof : Slice U8} {raw : Array U32 22#usize} {batch : Usize}
 {calls : List NLL_Parent.Call} {idx : NLL.Indices} {val : NLL.Values} {history : NLL.History} {out : NLL.Reply}
 {trace : SdkC_Source.Log} (native : NNC_C04Events.Returned H proof raw batch calls idx val history out trace) :
 ∀ q ∈ trace, Canonical q := by
 induction native with
 | nil idx val => intro q member; cases member
 | error root kind rest idx nextIdx val nextVal events error child => exact tree kind events
 | next root kind rest idx nextIdx val nextVal events tailHistory out trace child tail ih =>
   intro q member
   rcases List.mem_append.mp member with head | rest
   · exact tree kind events q head
   · exact ih q rest

/-- Upgrade the CLOSED returning history equation to the full RSL digest
chronology, preserving every original byte partition and reply. -/
theorem returned {H : Bytes → State} {proof : Slice U8} {raw : Array U32 22#usize} {batch : Usize}
 {calls : List NLL_Parent.Call} {idx : NLL.Indices} {val : NLL.Values} {history : NLL.History} {out : NLL.Reply}
 {trace : SdkC_Source.Log} (native : NNC_C04Events.Returned H proof raw batch calls idx val history out trace) :
 NNC_DigestTrace.render (trace.map NNC_DigestTrace.Step.attempted) = LIBB_C04LogGraph.render history :=
 (LIBB_C04LogGraph.log trace (shapes native)).trans
  (congrArg LIBB_C04LogGraph.render (NNC_C04Events.returning_read native))
#print axioms tree
#print axioms shapes
#print axioms returned
end LIBB_C04RichTrace
end
