import Lean
import NFN_PhaseTransport
import NFN_ReserveOwner
import NFN_GeometryPart05
import KMX_CopyMeaning

-- BEGIN copied NFB_GatherTrace: evidence/slice-q-compose5-20261104/NFB_GatherTrace.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NFB_GatherTrace
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NFN_NEW_GeometryDictionary
abbrev It := core.slice.iter.Iter U32
abbrev Vec := alloc.vec.Vec U32
abbrev Answer := core.result.Result AspisR1Stage2.verifier.QueryGeometry AspisR1Stage2.verifier.Error
abbrev Row := Port4C_GeometryGather.Row

def run (start : Usize) (it : It) (lines flat : Vec) : Result Answer :=
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0 adopted it start lines flat

/-- One SAME-state trace, including failures, divergence and early rejection.
Every continuation retains its actual query and both exact mutable outputs. -/
inductive Trace (start : Usize) : It → Vec → Vec → Result Answer → Prop
 | failed (it : It) (lines flat : Vec) (e : Aeneas.Std.Error)
     (observed : Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted start it lines flat=fail e) :
     Trace start it lines flat (fail e)
 | diverged (it : It) (lines flat : Vec)
     (observed : Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted start it lines flat=div) :
     Trace start it lines flat div
 | done (it : It) (lines flat : Vec) (value : Answer)
     (observed : Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted start it lines flat=ok (ControlFlow.done value)) :
     Trace start it lines flat (ok value)
 | step (it : It) (lines flat : Vec) (it1 : It) (lines1 flat1 : Vec)
     (query : U32) (row : Row) (result : Result Answer)
     (next : core.slice.iter.IteratorSliceIter.next it=ok (some query,it1))
     (observed : Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted start it lines flat=ok (cont (it1,lines1,flat1)))
     (sameSlice : it1.slice=it.slice) (cursor : it1.i=it.i+1)
     (flatFrame : flat1.val=flat.val++row.words)
     (lineFrame : lines1.val=lines.val++[row.lineZ])
     (nonzero : ∀ x∈row.words,x≠0#u32)
     (tail : Trace start it1 lines1 flat1 result) : Trace start it lines flat result

/-- Trace existence is DERIVED from the actual adopted partial computation;
there is no inner success, independently selected output, or trace premise. -/
theorem complete (start : Usize) (it : It) (lines flat : Vec) (fuel : Nat)
    (remaining : it.i+fuel=it.slice.val.length) :
    Trace start it lines flat (run start it lines flat) := by
 induction fuel generalizing it lines flat with
 | zero =>
   have next : core.slice.iter.IteratorSliceIter.next it=ok (none,it) :=
    NFN_NFB_QueryIterator.end_next it (by omega)
   unfold run Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0
   rw [loop.eq_def]
   simp only [uncurry]
   cases observed : Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted start it lines flat with
   | fail e => exact Trace.failed it lines flat e observed
   | div => exact Trace.diverged it lines flat observed
   | ok flow =>
    cases flow with
    | done value => exact Trace.done it lines flat value observed
    | cont after =>
     rcases after with ⟨it1,lines1,flat1⟩
     have impossible := Port4C_GeometryControl.terminal_not_cont adopted start it it it1
       lines flat lines1 flat1 next
     rw [NFN_NFB_GeometryInstall.standard] at impossible
     exact False.elim (impossible observed)
 | succ fuel ih =>
   have active : it.i < it.slice.val.length := by omega
   let query := it.slice.val[it.i]
   let it1 : It := {it with i:=it.i+1}
   have next : core.slice.iter.IteratorSliceIter.next it=ok (some query,it1) :=
    NFN_NFB_QueryIterator.next it active
   unfold run Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0
   rw [loop.eq_def]
   simp only [uncurry]
   cases observed : Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted start it lines flat with
   | fail e => exact Trace.failed it lines flat e observed
   | div => exact Trace.diverged it lines flat observed
   | ok flow =>
    cases flow with
    | done value => exact Trace.done it lines flat value observed
    | cont after =>
     rcases after with ⟨itOut,lines1,flat1⟩
     have sourceStep : Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body
         (Port4C_GeometryStd.install adopted) start it lines flat=ok (cont (itOut,lines1,flat1)) := by
      rw [NFN_NFB_GeometryInstall.standard]
      exact observed
     obtain ⟨row,u,parent,left,right,fibre,fleft,fright,point,square,doubled,one,fields⟩ :=
       Port4C_GeometryGather.step adopted start it it1 itOut query lines lines1 flat flat1 next sourceStep
     rcases fields with ⟨same,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,nonzero,hflat,hlines⟩
     subst itOut
     have tail := ih it1 lines1 flat1 (by dsimp only [it1];omega)
     exact Trace.step it lines flat it1 lines1 flat1 query row _ next observed rfl rfl hflat hlines nonzero tail

#print axioms complete
end NFN_NFB_GatherTrace
end
-- END copied NFB_GatherTrace
-- BEGIN copied NFB_GatherChain: evidence/slice-q-compose5-20261104/NFB_GatherChain.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NFB_GatherChain
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NFN_NFB_GatherTrace NFN_NEW_GeometryDictionary

def stopped (result : Result Answer) : Result (ControlFlow (It × Vec × Vec) Answer) :=
 match result with
 | .ok value => .ok (.done value)
 | .fail e => .fail e
 | .div => .div

/-- Every complete partial computation gives ONE ordered append/frame chain
and ONE terminal body on its SAME two final buffers, including error exits.
The terminal body retains the prefix/inverse/reverse/collect calls unchanged. -/
theorem chain (start : Usize) {it : It} {lines flat : Vec} {result : Result Answer}
    (trace : Trace start it lines flat result) :
    ∃ (rows : List Row) (terminal : It) (finalLines finalFlat : Vec),
      NFN_NET_GeometryGather.Trace (rows.map (fun r => (r.words,r.lineZ)))
        flat.val lines.val finalFlat.val finalLines.val ∧
      terminal.slice=it.slice ∧ terminal.i=it.i+rows.length ∧
      Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted
        start terminal finalLines finalFlat=stopped result := by
 induction trace with
 | failed it lines flat e observed =>
   exact ⟨[],it,lines,flat,NFN_NET_GeometryGather.Trace.done _ _,rfl,by simp,observed⟩
 | diverged it lines flat observed =>
   exact ⟨[],it,lines,flat,NFN_NET_GeometryGather.Trace.done _ _,rfl,by simp,observed⟩
 | done it lines flat value observed =>
   exact ⟨[],it,lines,flat,NFN_NET_GeometryGather.Trace.done _ _,rfl,by simp,observed⟩
 | step it lines flat it1 lines1 flat1 query row result next observed sameSlice cursor hflat hlines nonzero tail ih =>
   obtain ⟨rows,terminal,finalLines,finalFlat,frames,sliceEq,indexEq,terminalRun⟩ := ih
   refine ⟨row::rows,terminal,finalLines,finalFlat,?_,sliceEq.trans sameSlice,?_,terminalRun⟩
   · exact NFN_NET_GeometryGather.Trace.step (row.words,row.lineZ)
       (rows.map (fun r => (r.words,r.lineZ))) flat.val lines.val flat1.val lines1.val
       finalFlat.val finalLines.val hflat hlines
       (by simp only [Port4C_GeometryGather.Row.words,List.length_cons,List.length_nil]) frames
   · simp only [List.length_cons]
     omega

/-- Prefix lengths, exact ordered contents and terminal cursor are all
DERIVED from the SAME full computation, not caller-supplied output choices. -/
theorem complete (start : Usize) (it : It) (lines flat : Vec) (fuel : Nat)
    (remaining : it.i+fuel=it.slice.val.length) :
    ∃ (rows : List Row) (terminal : It) (finalLines finalFlat : Vec),
      finalFlat.val=flat.val++(rows.flatMap (fun r => r.words)) ∧
      finalLines.val=lines.val++(rows.map (fun r => r.lineZ)) ∧
      finalFlat.val.length=flat.val.length+5*rows.length ∧
      finalLines.val.length=lines.val.length+rows.length ∧
      terminal.slice=it.slice ∧ terminal.i=it.i+rows.length ∧
      Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted
        start terminal finalLines finalFlat=stopped (run start it lines flat) := by
 obtain ⟨rows,terminal,finalLines,finalFlat,frames,sliceEq,indexEq,terminalRun⟩ :=
   chain start (NFN_NFB_GatherTrace.complete start it lines flat fuel remaining)
 obtain ⟨flatMeaning,lineMeaning⟩ := NFN_NET_GeometryGather.meaning frames
 obtain ⟨flatLength,lineLength⟩ := NFN_NET_GeometryGather.lengths frames
 refine ⟨rows,terminal,finalLines,finalFlat,?_,?_,?_,?_,sliceEq,indexEq,terminalRun⟩
 · simpa only [List.flatMap_map,Function.comp_def] using flatMeaning
 · simpa only [List.map_map,Function.comp_def] using lineMeaning
 · simpa only [List.length_map] using flatLength
 · simpa only [List.length_map] using lineLength

#print axioms chain
#print axioms complete
end NFN_NFB_GatherChain
end
-- END copied NFB_GatherChain
-- BEGIN copied NFB_RangeTrace: evidence/slice-q-compose5-20261104/NFB_RangeTrace.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NFB_RangeTrace
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NFN_NEW_GeometryRawInterface NFN_NEW_GeometryDictionary NFN_NFB_GatherTrace
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

def Deployed (start finish : Usize) : Prop :=
 (start=0#usize ∧ finish=10#usize) ∨ (start=10#usize ∧ finish=22#usize)

theorem bounds (start finish : Usize) (scope : Deployed start finish) :
 start.val≤finish.val ∧ finish.val≤22 ∧
 (finish.val-start.val=10 ∨ finish.val-start.val=12) := by
 rcases scope with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide

/-- The actual selected query view is a precise window of the SAME original
array, with no fixed-query fixture or accepted-root premise. -/
theorem selected (queries : Array U32 22#usize) (start finish : Usize)
    (order : start.val≤finish.val) (bound : finish.val≤22) :
 ∃ slice : Slice U32,
  Port4C_GeometryRange.selected queries start finish=ok slice ∧
  slice.val=(queries.val.drop start.val).take (finish.val-start.val) ∧
  slice.val.length=finish.val-start.val := by
 obtain ⟨slice,read,contents,length⟩ := WP.spec_imp_exists
   (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
     (⟨start,finish⟩ : core.ops.range.Range Usize) (Array.to_slice queries) order
     (by change finish.val≤queries.val.length;rw [queries.property];exact bound))
 refine ⟨slice,read,?_,length⟩
 change slice.val=queries.val.extract start.val finish.val at contents
 simpa only [List.extract_eq_drop_take] using contents

/-- Root association for every raw query array. Trace existence and both
initial empty buffers come from the SAME actual-emitted Result. No inner
trace, child success, domain dictionary, or whole-buffer answer is supplied. -/
theorem complete (queries : Array U32 22#usize) (start finish : Usize)
    (order : start.val≤finish.val) (bound : finish.val≤22) :
 ∃ slice : Slice U32,
  Port4C_GeometryRange.selected queries start finish=ok slice ∧
  slice.val=(queries.val.drop start.val).take (finish.val-start.val) ∧
  slice.val.length=finish.val-start.val ∧
  Trace start ⟨slice,0⟩ (alloc.vec.Vec.new U32) (alloc.vec.Vec.new U32)
   (resultMap answer (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish)) := by
 obtain ⟨slice,read,contents,length⟩ := selected queries start finish order bound
 have root : Port3_NativeGeometryBody.verifier.QueryGeometry.for_range adopted queries start finish=
     run start ⟨slice,0⟩ (alloc.vec.Vec.new U32) (alloc.vec.Vec.new U32) := by
  rw [Port4C_GeometryRange.native_range adopted queries start finish order bound,read,bind_tc_ok]
  rfl
 refine ⟨slice,read,contents,length,?_⟩
 rw [NFN_NEW_GeometryComplete.complete_raw,root]
 exact NFN_NFB_GatherTrace.complete start ⟨slice,0⟩ (alloc.vec.Vec.new U32)
   (alloc.vec.Vec.new U32) (finish.val-start.val) (by simp only;omega)

#print axioms bounds
#print axioms selected
#print axioms complete
end NFN_NFB_RangeTrace
end
-- END copied NFB_RangeTrace
-- BEGIN copied NFB_ActualStep: evidence/slice-q-compose5-20261104/NFB_ActualStep.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NFB_ActualStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NFN_NEW_GeometryRawInterface NFN_NEW_GeometryDictionary NFN_NFB_GatherTrace
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

theorem continuation (start : Usize) (it it1 : It) (lines flat lines1 flat1 : Vec)
 (observed : Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body
 adopted start it lines flat=ok (cont (it1,lines1,flat1))) :
 NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0.body start it lines flat=
 ok (cont (it1,lines1,flat1)) := by
 have associated := NFN_NFB_GeometryInstall.step start it lines flat
 rw [observed] at associated
 cases h : NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0.body start it lines flat with
 | fail e => simp [h,resultMap] at associated
 | div => simp [h,resultMap] at associated
 | ok flow =>
  cases flow with
  | done value => simp [h,resultMap,NEW_LoopMap.flowMap] at associated
  | cont state =>
   simp only [h,resultMap,NEW_LoopMap.flowMap,Result.ok.injEq,ControlFlow.cont.injEq] at associated
   cases associated
   rfl

/-- Rejected and divergent terminal cuts are exact partial Results too. -/
theorem failed (start : Usize) (it : It) (lines flat : Vec) (error : Aeneas.Std.Error)
 (observed : Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body
 adopted start it lines flat=fail error) :
 NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0.body start it lines flat=fail error := by
 have associated := NFN_NFB_GeometryInstall.step start it lines flat
 rw [observed] at associated
 cases h : NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0.body start it lines flat <;>
  simp_all [resultMap]
#print axioms continuation
#print axioms failed
end NFN_NFB_ActualStep
end
-- END copied NFB_ActualStep
-- BEGIN copied NFB_PhysicalFrame: evidence/slice-q-compose5-20261104/NFB_PhysicalFrame.lean
set_option autoImplicit false
namespace NFN_NFB_PhysicalFrame
open Aeneas.Std

/-- Allocation identities, rather than equal contents, select physical places.
The interpretation of these identities in native memory is P6. -/
abbrev Heap := Nat → Option (List U32)

def write (heap : Heap) (owner : Nat) (value : Option (List U32)) : Heap :=
  fun place => if place=owner then value else heap place

inductive Action where
 | allocate (owner : Nat) (value : List U32)
 | store (owner offset : Nat) (value : U32)
 | append (owner : Nat) (values : List U32)
 | release (owner : Nat)

def Action.owner : Action → Nat
 | .allocate o _ | .store o _ _ | .append o _ | .release o => o

def Action.apply (action : Action) (heap : Heap) : Heap :=
 match action with
 | .allocate o v => write heap o (some v)
 | .store o j v => write heap o ((heap o).map (fun xs => xs.set j v))
 | .append o v => write heap o ((heap o).map (fun xs => xs++v))
 | .release o => write heap o none

def run : List Action → Heap → Heap
 | [],heap => heap
 | action::tail,heap => run tail (action.apply heap)

theorem other_place (action : Action) (heap : Heap) (place : Nat)
    (disjoint : place ≠ action.owner) : action.apply heap place=heap place := by
 cases action <;> simp only [Action.apply,Action.owner] at * <;>
   simp only [write,disjoint,if_false]

/-- No update, allocation or release in the actual ordered private-buffer
trace can change the protected allocation. Repeated writes keep SAME identity. -/
theorem trace_frame (actions : List Action) (heap : Heap) (place : Nat)
    (disjoint : ∀ a ∈ actions, place≠a.owner) : run actions heap place=heap place := by
 induction actions generalizing heap with
 | nil => rfl
 | cons action tail ih =>
   rw [run,ih (action.apply heap) (fun a ha => disjoint a (List.mem_cons_of_mem action ha))]
   exact other_place action heap place (disjoint action (List.mem_cons_self))

/-- Extensional observation of the SAME owner reconstructs its whole payload;
a separately selected buffer with equal length is insufficient. -/
theorem same_payload (heap : Heap) (owner : Nat) (before after : List U32)
    (selected : heap owner=some after) (size : after.length=before.length)
    (windows : ∀ j, j<before.length → after[j]?=before[j]?) :
    heap owner=some before := by
 have same : after=before := by
  apply List.ext_getElem?
  intro j
  by_cases h : j<before.length
  · exact windows j h
  · rw [List.getElem?_eq_none (by omega : after.length≤j),
      List.getElem?_eq_none (by omega : before.length≤j)]
 rw [selected,same]

/-- Frame transport also covers a rejected finite prefix; no accepted-only
restriction is used. -/
theorem prefix_frame (actions : List Action) (heap : Heap) (place count : Nat)
    (disjoint : ∀ a ∈ actions, place≠a.owner) :
    run (actions.take count) heap place=heap place := by
 apply trace_frame
 intro a ha
 exact disjoint a (List.mem_of_mem_take ha)

#print axioms other_place
#print axioms trace_frame
#print axioms same_payload
#print axioms prefix_frame
end NFN_NFB_PhysicalFrame
-- END copied NFB_PhysicalFrame
-- BEGIN copied NFB_PrivateFrame: evidence/slice-q-compose5-20261104/NFB_PrivateFrame.lean
set_option autoImplicit false
namespace NFN_NFB_PrivateFrame
open Aeneas.Std NFN_NFB_PhysicalFrame

/-- Private allocation slots cannot designate the root's protected query place.
The native interpretation maps these slots to fresh owned allocations. -/
inductive Place where
 | flat | lines | prefixes | inverse | rows
 deriving DecidableEq

def Place.id : Place → Nat
 | .flat => 1 | .lines => 2 | .prefixes => 3 | .inverse => 4 | .rows => 5

def allocate (place : Place) (value : List U32) : Action := .allocate place.id value
def store (place : Place) (offset : Nat) (value : U32) : Action := .store place.id offset value
def append (place : Place) (value : List U32) : Action := .append place.id value
def release (place : Place) : Action := .release place.id

inductive Private : Action → Prop where
 | allocate (p : Place) (v : List U32) : Private (allocate p v)
 | store (p : Place) (j : Nat) (v : U32) : Private (store p j v)
 | append (p : Place) (v : List U32) : Private (append p v)
 | release (p : Place) : Private (release p)

theorem disjoint (a : Action) (h : Private a) : 0≠a.owner := by
 cases h with
 | allocate p v => cases p <;> simp only [allocate,Action.owner,Place.id] <;> omega
 | store p j v => cases p <;> simp only [store,Action.owner,Place.id] <;> omega
 | append p v => cases p <;> simp only [append,Action.owner,Place.id] <;> omega
 | release p => cases p <;> simp only [release,Action.owner,Place.id] <;> omega

/-- Any prefix, including one ending at a rejection, preserves the SAME
protected query allocation. This is the ownership induction, not a native
receipt; the source/trace association must separately instantiate Private. -/
theorem protected_query (actions : List Action) (heap : Heap) (count : Nat)
    (owned : ∀ a∈actions, Private a) :
    run (actions.take count) heap 0=heap 0 := by
 apply prefix_frame
 intro a ha
 exact disjoint a (owned a ha)

#print axioms disjoint
#print axioms protected_query
end NFN_NFB_PrivateFrame
-- END copied NFB_PrivateFrame
-- BEGIN copied NFB_GatherFrame: evidence/slice-q-compose5-20261104/NFB_GatherFrame.lean
set_option autoImplicit false
namespace NFN_NFB_GatherFrame
open Aeneas.Std NFN_NFB_PhysicalFrame NFN_NFB_PrivateFrame NFN_NFB_GatherTrace

def actions : List Row → List Action
 | [] => []
 | r::rs => append .flat r.words :: append .lines [r.lineZ] :: actions rs

theorem owned (rows : List Row) : ∀ a∈actions rows, Private a := by
 induction rows with
 | nil => simp [actions]
 | cons r rs ih =>
  intro a ha
  simp only [actions,List.mem_cons] at ha
  rcases ha with rfl | rfl | ha
  · exact Private.append _ _
  · exact Private.append _ _
  · exact ih a ha

theorem query_frame (rows : List Row) (heap : Heap) (count : Nat) :
 run ((actions rows).take count) heap 0=heap 0 :=
 protected_query (actions rows) heap count (owned rows)

/-- The ordered two-owner writes reconstruct both buffers in the SAME heap. -/
theorem payloads (rows : List Row) (heap : Heap) (flat lines : List U32)
 (hflat : heap Place.flat.id=some flat) (hlines : heap Place.lines.id=some lines) :
 run (actions rows) heap Place.flat.id=some (flat++rows.flatMap (fun r=>r.words)) ∧
 run (actions rows) heap Place.lines.id=some (lines++rows.map (fun r=>r.lineZ)) := by
 induction rows generalizing heap flat lines with
 | nil => simp [actions,NFN_NFB_PhysicalFrame.run,hflat,hlines]
 | cons r rs ih =>
  let next := (append .lines [r.lineZ]).apply ((append .flat r.words).apply heap)
  have hf : next Place.flat.id=some (flat++r.words) := by
   simp only [Place.id] at hflat
   simp [next,append,Action.apply,write,Place.id,hflat]
  have hl : next Place.lines.id=some (lines++[r.lineZ]) := by
   simp only [Place.id] at hlines
   simp [next,append,Action.apply,write,Place.id,hlines]
  have result := ih next (flat++r.words) (lines++[r.lineZ]) hf hl
  simpa [actions,NFN_NFB_PhysicalFrame.run,next,List.flatMap_cons,List.map_cons,List.append_assoc] using result
#print axioms owned
#print axioms query_frame
#print axioms payloads
end NFN_NFB_GatherFrame
-- END copied NFB_GatherFrame
-- BEGIN copied NFB_RootGather: evidence/slice-q-compose5-20261104/NFB_RootGather.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NFB_RootGather
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NFN_NEW_GeometryRawInterface NFN_NEW_GeometryDictionary NFN_NFB_GatherTrace
open NFN_NFB_PhysicalFrame NFN_NFB_PrivateFrame
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

/-- Physical gather association. The SAME ordered heap writes and terminal
buffers are derived from the actual root, for every raw query array. -/
theorem complete (queries : Array U32 22#usize) (start finish : Usize)
 (order : start.val≤finish.val) (bound : finish.val≤22) (heap : Heap)
 (emptyFlat : heap Place.flat.id=some []) (emptyLines : heap Place.lines.id=some []) :
 ∃ (slice : Slice U32) (rows : List Row) (terminal : It) (lines flat : Vec),
  slice.val=(queries.val.drop start.val).take (finish.val-start.val) ∧
  terminal.slice=slice ∧ terminal.i=rows.length ∧
  flat.val=rows.flatMap (fun r=>r.words) ∧ lines.val=rows.map (fun r=>r.lineZ) ∧
  NFN_NFB_PhysicalFrame.run (NFN_NFB_GatherFrame.actions rows) heap Place.flat.id=some flat.val ∧
  NFN_NFB_PhysicalFrame.run (NFN_NFB_GatherFrame.actions rows) heap Place.lines.id=some lines.val ∧
  (∀ count, NFN_NFB_PhysicalFrame.run ((NFN_NFB_GatherFrame.actions rows).take count) heap 0=heap 0) ∧
  Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted
   start terminal lines flat=NFN_NFB_GatherChain.stopped
    (resultMap answer (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish)) := by
 obtain ⟨slice,read,window,length,trace⟩ := NFN_NFB_RangeTrace.complete queries start finish order bound
 obtain ⟨rows,terminal,lines,flat,frames,same,cursor,terminalRun⟩ := NFN_NFB_GatherChain.chain start trace
 obtain ⟨flatMeaning,lineMeaning⟩ := NFN_NET_GeometryGather.meaning frames
 have hf : flat.val=rows.flatMap (fun r=>r.words) := by
  simpa only [alloc.vec.Vec.new,List.nil_append,List.flatMap_map,Function.comp_def] using flatMeaning
 have hl : lines.val=rows.map (fun r=>r.lineZ) := by
  simpa only [alloc.vec.Vec.new,List.nil_append,List.map_map,Function.comp_def] using lineMeaning
 obtain ⟨physicalFlat,physicalLines⟩ := NFN_NFB_GatherFrame.payloads rows heap [] [] emptyFlat emptyLines
 refine ⟨slice,rows,terminal,lines,flat,window,same,?_,hf,hl,?_,?_,?_,terminalRun⟩
 · simpa only [Nat.zero_add] using cursor
 · simpa only [List.nil_append,←hf] using physicalFlat
 · simpa only [List.nil_append,←hl] using physicalLines
 · exact fun count=>NFN_NFB_GatherFrame.query_frame rows heap count
#print axioms complete
end NFN_NFB_RootGather
end
-- END copied NFB_RootGather
-- BEGIN copied NFB_TraceBounds: evidence/slice-q-compose5-20261104/NFB_TraceBounds.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NFB_TraceBounds
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NFN_NEW_GeometryDictionary NFN_NFB_GatherTrace

theorem next_active (it it1 : It) (query : U32)
 (next : core.slice.iter.IteratorSliceIter.next it=ok (some query,it1)) :
 it.i < it.slice.val.length := by
 unfold core.slice.iter.IteratorSliceIter.next at next
 split at next
 · assumption
 · cases next

theorem terminal_bound (start : Usize) {it : It} {lines flat : Vec} {result : Result Answer}
 (trace : Trace start it lines flat result) (within : it.i ≤ it.slice.val.length) :
 ∃ (rows : List Row) (terminal : It) (finalLines finalFlat : Vec),
 NFN_NET_GeometryGather.Trace (rows.map (fun r=>(r.words,r.lineZ)))
  flat.val lines.val finalFlat.val finalLines.val ∧
 terminal.slice=it.slice ∧ terminal.i=it.i+rows.length ∧
 terminal.i ≤ terminal.slice.val.length ∧
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted
  start terminal finalLines finalFlat=NFN_NFB_GatherChain.stopped result := by
 revert within
 induction trace with
 | failed it lines flat e observed =>
  intro within
  exact ⟨[],it,lines,flat,.done _ _,rfl,by simp,within,observed⟩
 | diverged it lines flat observed =>
  intro within
  exact ⟨[],it,lines,flat,.done _ _,rfl,by simp,within,observed⟩
 | done it lines flat value observed =>
  intro within
  exact ⟨[],it,lines,flat,.done _ _,rfl,by simp,within,observed⟩
 | step it lines flat it1 lines1 flat1 query row result next observed sameSlice cursor hf hl nz tail ih =>
  intro within
  have active := next_active it it1 query next
  have within1 : it1.i ≤ it1.slice.val.length := by rw [sameSlice,cursor];omega
  obtain ⟨rows,terminal,finalLines,finalFlat,frames,same,index,limit,last⟩ := ih within1
  refine ⟨row::rows,terminal,finalLines,finalFlat,?_,same.trans sameSlice,?_,limit,last⟩
  · exact NFN_NET_GeometryGather.Trace.step (row.words,row.lineZ) _ _ _ _ _ _ _ hf hl
     (by simp only [Port4C_GeometryGather.Row.words,List.length_cons,List.length_nil]) frames
  · simp only [List.length_cons]
    omega

theorem accepted_end (start : Usize) (it : It) (lines flat : Vec)
 (out : AspisR1Stage2.verifier.QueryGeometry) (within : it.i ≤ it.slice.val.length)
 (accepted : Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body
 adopted start it lines flat=ok (done (.Ok out))) : it.i=it.slice.val.length := by
 by_contra h
 have active : it.i < it.slice.val.length := by omega
 have next:=NFN_NFB_QueryIterator.next it active
 have impossible:=Port4C_GeometryControl.active_not_done adopted start it
  {it with i:=it.i+1} it.slice.val[it.i] lines flat out next
 rw [NFN_NFB_GeometryInstall.standard] at impossible
 exact impossible accepted
#print axioms next_active
#print axioms terminal_bound
#print axioms accepted_end
end NFN_NFB_TraceBounds
end
-- END copied NFB_TraceBounds
-- BEGIN copied NFB_AcceptedGather: evidence/slice-q-compose5-20261104/NFB_AcceptedGather.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NFB_AcceptedGather
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NFN_NEW_GeometryRawInterface NFN_NEW_GeometryDictionary NFN_NFB_GatherTrace
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

theorem complete (queries : Array U32 22#usize) (start finish : Usize)
 (order : start.val≤finish.val) (bound : finish.val≤22)
 (out : AspisR1Stage2.verifier.QueryGeometry)
 (accepted : resultMap answer
  (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish)=ok (.Ok out)) :
 ∃ (rows : List Row) (terminal : It) (lines flat : Vec),
 rows.length=finish.val-start.val ∧
 flat.val=rows.flatMap (fun r=>r.words) ∧ lines.val=rows.map (fun r=>r.lineZ) ∧
 flat.val.length=5*(finish.val-start.val) ∧ lines.val.length=finish.val-start.val ∧
 terminal.i=terminal.slice.val.length ∧
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted
  start terminal lines flat=ok (done (.Ok out)) := by
 obtain ⟨slice,read,window,length,trace⟩ := NFN_NFB_RangeTrace.complete queries start finish order bound
 rw [accepted] at trace
 obtain ⟨rows,terminal,lines,flat,frames,same,cursor,within,last⟩ :=
  NFN_NFB_TraceBounds.terminal_bound start trace (by change 0≤slice.val.length;omega)
 have ending := NFN_NFB_TraceBounds.accepted_end start terminal lines flat out within last
 change terminal.slice=slice at same
 change terminal.i=0+rows.length at cursor
 have count : rows.length=finish.val-start.val := by
  simp only [Nat.zero_add] at cursor
  rw [same,length] at ending
  omega
 obtain ⟨flatMeaning,lineMeaning⟩ := NFN_NET_GeometryGather.meaning frames
 obtain ⟨flatLength,lineLength⟩ := NFN_NET_GeometryGather.lengths frames
 refine ⟨rows,terminal,lines,flat,count,?_,?_,?_,?_,ending,last⟩
 · simpa only [alloc.vec.Vec.new,List.nil_append,List.flatMap_map,Function.comp_def] using flatMeaning
 · simpa only [alloc.vec.Vec.new,List.nil_append,List.map_map,Function.comp_def] using lineMeaning
 · simpa only [alloc.vec.Vec.new,List.length_nil,List.length_map,Nat.zero_add,count] using flatLength
 · simpa only [alloc.vec.Vec.new,List.length_nil,List.length_map,Nat.zero_add,count] using lineLength
#print axioms complete
end NFN_NFB_AcceptedGather
end
-- END copied NFB_AcceptedGather
-- BEGIN copied NFB_TerminalCuts: evidence/slice-q-compose5-20261104/NFB_TerminalCuts.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NFB_TerminalCuts
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NFN_NEW_GeometryDictionary NFN_NFB_GatherTrace
open Port3_PushFrame (bind_success)

/-- Every terminal success obtains its intermediate buffers from THIS run.
No prefix, inverse or collected output is supplied independently. -/
theorem complete (start : Usize) (it : It) (lines flat : Vec)
 (out : AspisR1Stage2.verifier.QueryGeometry)
 (ending : it.i=it.slice.val.length) (notempty : flat.val≠[])
 (accepted : Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body
 adopted start it lines flat=ok (done (.Ok out))) :
 ∃ (prefixes : Vec) (product suffix zero : U32) (resized inverse : Vec)
   (rev : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
   (mapped : core.iter.adapters.map.Map (core.ops.range.Range Usize) Vec)
   (groups : alloc.vec.Vec (Array U32 5#usize)),
 adopted.op13 flat.deref=ok (prefixes,product) ∧
 adopted.op11 product=ok suffix ∧ adopted.op6=ok zero ∧
 alloc.vec.Vec.resize core.marker.CopyU32.cloneInst
  (alloc.vec.Vec.with_capacity U32 (alloc.vec.Vec.len flat)) (alloc.vec.Vec.len flat) zero=ok resized ∧
 core.iter.traits.iterator.Iterator.rev.trait_default
  (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
  (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
  {start:=0#usize,«end»:=alloc.vec.Vec.len flat}=ok rev ∧
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0 adopted
  rev flat prefixes suffix resized=ok inverse ∧
 adopted.op1
  (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
  (Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 adopted)
  {start:=0#usize,«end»:=alloc.vec.Vec.len lines} inverse=ok mapped ∧
 core.iter.traits.iterator.Iterator.collect.default
  (adopted.mapIterator (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
   (Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 adopted))
  (core.iter.traits.collect.FromIteratorVec (Array U32 5#usize)) mapped=ok groups ∧
 out.start=start ∧ out.line_z=lines ∧ out.inverses=groups := by
 have next := NFN_NFB_QueryIterator.end_next it (by omega)
 unfold Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body at accepted
 rw [next,bind_tc_ok] at accepted
 have empty : adopted.op4 Global flat=ok false := by
  change ok flat.val.isEmpty=ok false
  simp only [List.isEmpty_eq_false_iff.mpr notempty]
 rw [empty,bind_tc_ok] at accepted
 simp only [Bool.false_eq_true,if_false] at accepted
 obtain ⟨⟨prefixes,product⟩,hp,accepted⟩ := bind_success _ _ _ accepted
 obtain ⟨suffix,hs,accepted⟩ := bind_success _ _ _ accepted
 obtain ⟨zero,hz,accepted⟩ := bind_success _ _ _ accepted
 obtain ⟨resized,hr,accepted⟩ := bind_success _ _ _ accepted
 obtain ⟨rev,hv,accepted⟩ := bind_success _ _ _ accepted
 obtain ⟨inverse,hi,accepted⟩ := bind_success _ _ _ accepted
 obtain ⟨mapped,hm,accepted⟩ := bind_success _ _ _ accepted
 obtain ⟨groups,hg,accepted⟩ := bind_success _ _ _ accepted
 cases Result.ok.inj accepted
 exact ⟨prefixes,product,suffix,zero,resized,inverse,rev,mapped,groups,hp,hs,hz,hr,hv,hi,hm,hg,rfl,rfl,rfl⟩
#print axioms complete
end NFN_NFB_TerminalCuts
end
-- END copied NFB_TerminalCuts
-- BEGIN copied NFB_ReverseTrace: evidence/slice-q-compose5-20261104/NFB_ReverseTrace.lean
set_option autoImplicit false
namespace NFN_NFB_ReverseTrace
open Aeneas.Std AspisR1 NFN_NFB_PhysicalFrame NFN_NFB_PrivateFrame
open S7Kani2PrefixLoop (wordMul)
open Port4C_BatchInverse (cell)

def writes (flat prefixes : List U32) : Nat → U32 → List Action
 | 0,_ => []
 | n+1,s => store .inverse n (wordMul s (cell prefixes n)) ::
    writes flat prefixes n (wordMul s (cell flat n))

theorem complete (flat prefixes inverse : List U32) (n : Nat) (suffix : U32)
 (bound : n ≤ inverse.length) :
 NFN_NEW_GeometryReverse.Trace flat prefixes n inverse suffix
  (Port4C_OwnedInverse.model flat prefixes n inverse suffix)
  (NFN_NEW_GeometryReverse.suffixAfter flat n suffix)
  (NFN_NEW_GeometryReverse.callLog flat prefixes n suffix) := by
 induction n generalizing inverse suffix with
 | zero => exact NFN_NEW_GeometryReverse.Trace.done _ _
 | succ n ih =>
  apply NFN_NEW_GeometryReverse.Trace.step n inverse
   (inverse.set n (wordMul suffix (cell prefixes n)))
   (Port4C_OwnedInverse.model flat prefixes (n+1) inverse suffix)
   suffix (NFN_NEW_GeometryReverse.suffixAfter flat (n+1) suffix)
   (NFN_NEW_GeometryReverse.callLog flat prefixes n (wordMul suffix (cell flat n)))
  · omega
  · exact List.length_set
  · intro j hj
    by_cases same : j=n
    · subst j
      simp only [ite_true,List.getElem?_set_self (by omega : n < inverse.length)]
    · simp only [same,if_false,List.getElem?_set_ne (Ne.symm same)]
  · exact ih _ _ (by simpa only [List.length_set] using (show n ≤ inverse.length by omega))

theorem owned (flat prefixes : List U32) (n : Nat) (suffix : U32) :
 ∀ a∈writes flat prefixes n suffix,Private a := by
 induction n generalizing suffix with
 | zero => simp [writes]
 | succ n ih =>
  intro a ha
  simp only [writes,List.mem_cons] at ha
  rcases ha with rfl | ha
  · exact Private.store _ _ _
  · exact ih _ a ha

theorem payload (flat prefixes inverse : List U32) (n : Nat) (suffix : U32)
 (heap : Heap) (selected : heap Place.inverse.id=some inverse) :
 NFN_NFB_PhysicalFrame.run (writes flat prefixes n suffix) heap Place.inverse.id=
 some (Port4C_OwnedInverse.model flat prefixes n inverse suffix) := by
 induction n generalizing inverse suffix heap with
 | zero => exact selected
 | succ n ih =>
  change NFN_NFB_PhysicalFrame.run
   (writes flat prefixes n (wordMul suffix (cell flat n)))
   ((store .inverse n (wordMul suffix (cell prefixes n))).apply heap)
   Place.inverse.id=_
  apply ih
  simp only [store,Action.apply,write,ite_true,selected,Option.map_some,cell]
#print axioms complete
#print axioms owned
#print axioms payload
end NFN_NFB_ReverseTrace
-- END copied NFB_ReverseTrace
-- BEGIN copied NFB_ResizeTrace: evidence/slice-q-compose5-20261104/NFB_ResizeTrace.lean
set_option autoImplicit false
namespace NFN_NFB_ResizeTrace
open Aeneas.Std

/-- One native resize window reconstructs exactly one appended zero, retaining
all old values. Both observations concern the SAME before/after allocation. -/
theorem step (before after : List U32)
    (size : after.length=before.length+1)
    (old : ∀ j, j<before.length → after[j]?=before[j]?)
    (new : after[before.length]?=some 0#u32) : after=before++[0#u32] := by
 apply List.ext_getElem?
 intro j
 by_cases h : j<before.length
 · rw [old j h,List.getElem?_append_left h]
 · by_cases same : j=before.length
   · subst j
     rw [new,List.getElem?_append_right (by omega)]
     simp only [Nat.sub_self,List.getElem?_cons_zero]
   · rw [List.getElem?_eq_none (by omega : after.length≤j),
       List.getElem?_eq_none (by simp only [List.length_append,List.length_singleton]; omega)]

inductive Trace : Nat → List U32 → List U32 → Prop where
 | done (before : List U32) : Trace 0 before before
 | step (n : Nat) (before next final : List U32)
     (size : next.length=before.length+1)
     (old : ∀ j, j<before.length → next[j]?=before[j]?)
     (new : next[before.length]?=some 0#u32)
     (tail : Trace n next final) : Trace (n+1) before final

/-- Whole-buffer value law from one native iteration and an induction, without
unwinding a resize or assuming its whole output as a premise. -/
theorem complete {n : Nat} {before after : List U32} (trace : Trace n before after) :
    after=before++List.replicate n 0#u32 := by
 induction trace with
 | done => simp only [List.replicate_zero,List.append_nil]
 | step n before next final size old new tail ih =>
   rw [ih,step before next size old new,List.append_assoc]
   simp only [List.replicate_succ,List.singleton_append]

#print axioms step
#print axioms complete
end NFN_NFB_ResizeTrace
-- END copied NFB_ResizeTrace
-- BEGIN copied NFB_CollectorTrace: evidence/slice-q-compose5-20261104/NFB_CollectorTrace.lean
set_option autoImplicit false
namespace NFN_NFB_CollectorTrace
open Aeneas.Std

/-- Only initialized live payload is exposed. Publication remains zero until
SetLenOnDrop finishes; this models the pinned TrustedLen specialization. -/
structure Guard (A : Type) where
 initialized : List A
 published : Nat
 deriving Repr

def store {A : Type} (s : Guard A) (x : A) : Guard A :=
 ⟨s.initialized++[x],s.published⟩
def finish {A : Type} (s : Guard A) : Guard A :=
 ⟨s.initialized,s.initialized.length⟩
def fill {A : Type} : List A → Guard A → Guard A
 | [],s => s
 | x::xs,s => fill xs (store s x)

theorem stores {A : Type} (xs : List A) (s : Guard A) :
 (fill xs s).initialized=s.initialized++xs ∧ (fill xs s).published=s.published := by
 induction xs generalizing s with
 | nil => simp [fill]
 | cons x xs ih =>
  have h := ih (store s x)
  simpa [fill,store,List.append_assoc] using h

theorem complete {A : Type} (xs : List A) :
 finish (fill xs (⟨[],0⟩ : Guard A))=⟨xs,xs.length⟩ := by
 have h:=stores xs (⟨[],0⟩ : Guard A)
 simp only [List.nil_append] at h
 simp only [finish,h.1]

/-- Arbitrary old live windows and the new slot reconstruct one SAME-buffer
store. This law is shared by array initialization and row collection. -/
theorem window_step {A : Type} (before after : List A) (value : A)
 (size : after.length=before.length+1)
 (old : ∀ j,j<before.length → after[j]?=before[j]?)
 (new : after[before.length]?=some value) : after=before++[value] := by
 apply List.ext_getElem?
 intro j
 by_cases active : j<before.length
 · rw [old j active,List.getElem?_append_left active]
 · by_cases last : j=before.length
   · subst j
     rw [new,List.getElem?_append_right (by omega)]
     simp only [Nat.sub_self,List.getElem?_cons_zero]
   · rw [List.getElem?_eq_none (by omega : after.length≤j),
       List.getElem?_eq_none (by simp only [List.length_append,List.length_singleton];omega)]

inductive Trace {A : Type} : List A → Guard A → Guard A → Prop where
 | done (s : Guard A) : Trace [] s s
 | step (x : A) (xs : List A) (s next out : Guard A)
  (size : next.initialized.length=s.initialized.length+1)
  (old : ∀ j,j<s.initialized.length → next.initialized[j]?=s.initialized[j]?)
  (new : next.initialized[s.initialized.length]?=some x)
  (unpublished : next.published=s.published)
  (tail : Trace xs next out) : Trace (x::xs) s out

theorem meaning {A : Type} {xs : List A} {before after : Guard A}
 (trace : Trace xs before after) : after=fill xs before := by
 induction trace with
 | done => rfl
 | step x xs s next out size old new unpublished tail ih =>
  have h:=window_step s.initialized next.initialized x size old new
  have same : next=store s x := by cases next;cases s;simp_all [store]
  rw [ih,same]
  rfl
#print axioms stores
#print axioms complete
#print axioms window_step
#print axioms meaning
end NFN_NFB_CollectorTrace
-- END copied NFB_CollectorTrace
-- BEGIN copied NFB_CollectAssociation: evidence/slice-q-compose5-20261104/NFB_CollectAssociation.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NFB_CollectAssociation
open Aeneas Aeneas.Std Result AspisR1
open NFN_NFB_CollectorTrace
open NFN_NEW_GeometryDictionary

/-- The adopted collector and the native guard-local store induction have
ONE exact initialized payload and publication length. No child result premise. -/
theorem complete (flat : alloc.vec.Vec U32) (count : Usize)
 (bound : count.val≤22) (size : flat.val.length=5*count.val) :
 ∃ out : alloc.vec.Vec (Array U32 5#usize),
 Port4C_CollectLoop.collect (Port4C_GeometryInverse.install
  (NFN_NEB_ActualGeometryModel.install NFN_NEW_GeometryRawInterface.ops NFN_NEW_GeometryDictionary.err)) flat count=ok out ∧
 finish (fill ((List.range count.val).map (Port4C_CollectLoop.record flat))
  (⟨[],0⟩ : Guard (Array U32 5#usize)))=⟨out.val,out.val.length⟩ ∧
 out.val.length=count.val := by
 obtain ⟨out,run,contents,length⟩ := Port4C_CollectLoop.total
  (Port4C_GeometryInverse.install
   (NFN_NEB_ActualGeometryModel.install NFN_NEW_GeometryRawInterface.ops NFN_NEW_GeometryDictionary.err))
  flat count bound size
 refine ⟨out,run,?_,length⟩
 rw [NFN_NFB_CollectorTrace.complete,←contents]

/-- Five initialized native slots match every lane of the adopted callback. -/
theorem array_complete (flat : alloc.vec.Vec U32) (row : Nat) :
 finish (fill (Port4C_CollectLoop.record flat row).val (⟨[],0⟩ : Guard U32))=
 ⟨(Port4C_CollectLoop.record flat row).val,5⟩ := by
 rw [NFN_NFB_CollectorTrace.complete]
 congr 1
#print axioms complete
#print axioms array_complete
end NFN_NFB_CollectAssociation
end
-- END copied NFB_CollectAssociation

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
