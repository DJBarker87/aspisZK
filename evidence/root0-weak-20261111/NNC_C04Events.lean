import NNC_ResumeEvents
set_option autoImplicit false
noncomputable section
namespace NNC_C04Events
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 NLL NLL_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- The native node request retains BOTH native 32-byte buffers and the
actual hashv partition, rather than reconstructing parts from a flat address. -/
def nodes (events : List (NJP_RowModel.Request × NJP_RowModel.Digest)) : SdkC_Source.Log :=
 events.map (fun e => ⟨NJP_RequestTransport.address e.1, .ok (NJP_DigestCarrier.encode e.2)⟩)

/-- Exact returning syscall trace from actual tree cut events. Scalar events
have no syscall; leaf and node requests retain order, multiplicity and parts. -/
def tree (kind : Usize) (events : List NLL.Event) : SdkC_Source.Log :=
 events.flatMap (fun e => match e with
 | .leaf _ _ view digest => [⟨Port4B_LeafCode.input kind view,.ok digest⟩]
 | .verify _ _ _ requests _ => nodes requests
 | _ => [])

theorem read_append (a b : SdkC_Source.Log) :
 SdkC_Source.readLog (a++b) = SdkC_Source.readLog a ++ SdkC_Source.readLog b := by
 simp only [SdkC_Source.readLog,List.filterMap_append]

theorem nodes_read (events : List (NJP_RowModel.Request × NJP_RowModel.Digest)) :
 SdkC_Source.readLog (nodes events) = NJV_AdoptedObservation.history events := by
 induction events with
 | nil => rfl
 | cons e rest ih =>
   simp only [nodes,List.map_cons,SdkC_Source.readLog,List.filterMap_cons] at *
   simp only [NJV_AdoptedObservation.history,List.map_cons]
   exact congrArg (List.cons _) ih

theorem tree_one_read (kind : Usize) (e : NLL.Event) :
 SdkC_Source.readLog (tree kind [e]) = NLL.leafHistory kind [e] := by
 cases e <;> try rfl
 simpa only [tree,List.flatMap_cons,List.flatMap_nil,List.append_nil,
   NLL.leafHistory] using nodes_read _

theorem tree_read (kind : Usize) (events : List NLL.Event) :
 SdkC_Source.readLog (tree kind events) = NLL.leafHistory kind events := by
 induction events with
 | nil => rfl
 | cons e rest ih =>
   have appendTree : tree kind (e::rest) = tree kind [e] ++ tree kind rest := by
     simp only [tree,List.flatMap_cons,List.flatMap_nil,List.append_nil]
   have appendHistory : NLL.leafHistory kind (e::rest) =
     NLL.leafHistory kind [e] ++ NLL.leafHistory kind rest := by
     simp only [NLL.leafHistory,List.flatMap_cons,List.flatMap_nil,List.append_nil]
   rw [appendTree,read_append,tree_one_read,ih,appendHistory]

/-- Rich trace indexed by the SAME complete native parent/child calls.
No canonical Root0, source-model C04 equality or hash injectivity is used. -/
inductive Returned (H : Bytes → State) (proof : Slice U8) (raw : Array U32 22#usize) (batch : Usize) :
 List Call → NLL.Indices → NLL.Values → NLL.History → NLL.Reply → SdkC_Source.Log → Prop where
 | nil (idx : NLL.Indices) (val : NLL.Values) : Returned H proof raw batch [] idx val [] (.Ok ()) []
 | error (root : NLL.Root) (kind : Usize) (rest : List Call) (idx nextIdx : NLL.Indices) (val nextVal : NLL.Values)
   (events : List NLL.Event) (error : verifier.Error)
   (child : NLL.Invocation H proof raw root batch kind idx val events (.Err error,nextIdx,nextVal)) :
   Returned H proof raw batch ((root,kind)::rest) idx val (leafHistory kind events) (.Err error) (tree kind events)
 | next (root : NLL.Root) (kind : Usize) (rest : List Call) (idx nextIdx : NLL.Indices) (val nextVal : NLL.Values)
   (events : List NLL.Event) (tailHistory : NLL.History) (out : NLL.Reply) (trace : SdkC_Source.Log)
   (child : NLL.Invocation H proof raw root batch kind idx val events (.Ok (),nextIdx,nextVal))
   (tail : Returned H proof raw batch rest nextIdx nextVal tailHistory out trace) :
   Returned H proof raw batch ((root,kind)::rest) idx val (leafHistory kind events++tailHistory) out
     (tree kind events++trace)

theorem returning {H : Bytes → State} {proof : Slice U8} {raw : Array U32 22#usize} {batch : Usize}
 {calls : List Call} {idx : NLL.Indices} {val : NLL.Values} {history : NLL.History} {out : NLL.Reply}
 (native : Calls H proof raw batch calls idx val history out) :
 ∃ trace, Returned H proof raw batch calls idx val history out trace := by
 induction native with
 | nil idx val => exact ⟨[],.nil idx val⟩
 | error root kind rest idx nextIdx val nextVal events error child =>
   exact ⟨tree kind events,.error root kind rest idx nextIdx val nextVal events error child⟩
 | next root kind rest idx nextIdx val nextVal events tailHistory out child tail ih =>
   obtain ⟨trace,ih⟩ := ih
   exact ⟨tree kind events++trace,.next root kind rest idx nextIdx val nextVal events tailHistory out trace child ih⟩

theorem returning_read {H : Bytes → State} {proof : Slice U8} {raw : Array U32 22#usize} {batch : Usize}
 {calls : List Call} {idx : NLL.Indices} {val : NLL.Values} {history : NLL.History} {out : NLL.Reply}
 {trace : SdkC_Source.Log} (native : Returned H proof raw batch calls idx val history out trace) :
 SdkC_Source.readLog trace = history := by
 induction native with
 | nil => rfl
 | error => exact tree_read _ _
 | next root kind rest idx nextIdx val nextVal events tailHistory out trace child tail ih =>
   rw [read_append,tree_read,ih]

#print axioms read_append
#print axioms nodes_read
#print axioms tree_one_read
#print axioms tree_read
#print axioms returning
#print axioms returning_read
end NNC_C04Events
