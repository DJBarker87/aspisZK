import LIBB_C04RichTrace
import NNC_C04StopEvents
set_option autoImplicit false
noncomputable section
namespace LIBB_C04StoppedTrace
open Aeneas Aeneas.Std AspisR1
open AspisR1Stage2 MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open LIBB_C04LogGraph NNC_C04StopEvents

theorem pending_shapes {H : Bytes → State} {proof : Slice U8} {root : NLL.Root}
 {batch : Nat} {kind lo n slot : Usize} {f : NLL.Frame} {events : List NLL.Event} {pending : NLL.Pending}
 {trace : SdkC_Source.Log}
 (native : PendingTrace H proof root batch kind lo n slot f events pending trace) :
 ∀ q ∈ trace, Canonical q := by
 induction native with
 | leaf f more => intro q member; cases member
 | verify f done well fits padding queries q pending child => exact LIBB_C04LogGraph.nodes queries
 | next f t more step events pending trace tail ih => exact ih

theorem shapes {H : Bytes → State} {proof : Slice U8} {raw : Array U32 22#usize} {batch : Usize}
 {calls : List NLL_Parent.Call} {idx : NLL.Indices} {val : NLL.Values} {history : NLL.History} {pending : NLL.Pending}
 {trace : SdkC_Source.Log} (native : Stopped H proof raw batch calls idx val history pending trace) :
 ∀ q ∈ trace, Canonical q := by
 induction native with
 | here root kind rest idx val events pending trace child =>
   obtain ⟨rest,_,child⟩ := child
   intro q member
   rcases List.mem_append.mp member with head | tail
   · exact LIBB_C04RichTrace.tree kind events q head
   · exact pending_shapes child q tail
 | next root kind rest idx nextIdx val nextVal events history pending trace child tail ih =>
   intro q member
   rcases List.mem_append.mp member with head | rest
   · exact LIBB_C04RichTrace.tree kind events q head
   · exact ih q rest

/-- The pending request has no digest reply/event. All answered calls before
it remain in exact order, including completed leaves in the stopping tree. -/
theorem stopped {H : Bytes → State} {proof : Slice U8} {raw : Array U32 22#usize} {batch : Usize}
 {calls : List NLL_Parent.Call} {idx : NLL.Indices} {val : NLL.Values} {history : NLL.History} {pending : NLL.Pending}
 {trace : SdkC_Source.Log} (native : Stopped H proof raw batch calls idx val history pending trace) :
 NNC_DigestTrace.render (trace.map NNC_DigestTrace.Step.attempted ++ [.pending pending.parts]) =
 LIBB_C04LogGraph.render (history ++ pending.answered) := by
 rw [(NNC_DigestTrace.stopped trace pending.parts).2.2]
 exact (LIBB_C04LogGraph.log trace (shapes native)).trans
   (congrArg LIBB_C04LogGraph.render (NNC_C04StopEvents.stopped_read native))
#print axioms pending_shapes
#print axioms shapes
#print axioms stopped
end LIBB_C04StoppedTrace
end
