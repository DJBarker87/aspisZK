import NMB_TypedParent
set_option autoImplicit false
noncomputable section
namespace NMB_TypedParentFold
open Aeneas Aeneas.Std Result AspisR1 NMB_TypedParent
/-- Erases only instrumentation, preserving the complete parent result and
state. This is a SOURCE fold, not a physical parent-cut production theorem. -/
def erase (run : NMB_TypedParent.Run) : NMB_Stage1Source.Run :=
 ⟨run.result,run.post,run.events.map eraseEvent⟩
theorem copy (s : State) (saved : Bytes) :
 erase (NMB_TypedParent.copyResult s saved)=NMB_Stage1Source.copyResult s saved := by
 cases h : (NLQ_CopyTrace.G s.snapshots.sdk 2 s.snapshots.next
   (S2W_ReturnedCheckpoint.nativeBytes saved)).outcome <;>
 simp [NMB_TypedParent.copyResult,NMB_Stage1Source.copyResult,h,erase,eraseEvent,List.map_map] <;> rfl
theorem continuation (ops : AdapterRw.Ops) (p : Key) (d : Slice U8)
 (accounts : Slice NMB_Input.Owned) (s : State) :
 erase (NMB_TypedParent.continuation ops p d accounts s)=
 NMB_Stage1Source.continuation ops p d accounts s := by
 have resultEq := congrArg Prod.snd (NMB_OwnedTyped.forget_eq ops p accounts d)
 have eventsEq := NMB_OwnedResult.occurrences ops p accounts d
 change (NMB_OwnedTyped.stage1Owned ops p accounts d).result=_ at resultEq
 cases h : (NLD_Stage1Source.stage1Owned ops p accounts d).2 with
 | fail e => simp [NMB_TypedParent.continuation,NMB_Stage1Source.continuation,erase,eraseEvent,resultEq,eventsEq,h]
 | div => simp [NMB_TypedParent.continuation,NMB_Stage1Source.continuation,erase,eraseEvent,resultEq,eventsEq,h]
 | ok reply =>
  cases reply with
  | Err e => simp [NMB_TypedParent.continuation,NMB_Stage1Source.continuation,erase,eraseEvent,resultEq,eventsEq,h]
  | Ok saved =>
   have copied:=copy s saved
   simp only [erase] at copied
   simp [NMB_TypedParent.continuation,NMB_Stage1Source.continuation,erase,eraseEvent,resultEq,eventsEq,h]
   exact ⟨congrArg NMB_Stage1Source.Run.result copied,congrArg NMB_Stage1Source.Run.post copied,
    congrArg NMB_Stage1Source.Run.events copied⟩
/-- SAME snapshots, SAME child arguments, SAME post-world, all abort prefixes.
Only typed source instrumentation is forgotten; no native producer is assumed. -/
theorem source (x : NMB_Input.Input) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8)
 (alloc0 alloc1 alloc2 : Result Unit) :
 erase (NMB_TypedParent.G x ops p d alloc0 alloc1 alloc2)=
 NMB_Stage1Source.G x ops p d alloc0 alloc1 alloc2 := by
 cases h : (NMB_ThreeSnapshots.G x alloc0 alloc1 alloc2).result with
 | fail e => simp [NMB_TypedParent.G,NMB_Stage1Source.G,h,erase,eraseEvent,List.map_map]
 | div => simp [NMB_TypedParent.G,NMB_Stage1Source.G,h,erase,eraseEvent,List.map_map]
 | ok pair =>
  have tail:=continuation ops p d pair.1 ⟨pair.2,none⟩
  simp only [erase] at tail
  simp [NMB_TypedParent.G,NMB_Stage1Source.G,h,erase,eraseEvent,List.map_map,List.map_append]
  refine ⟨congrArg NMB_Stage1Source.Run.result tail,congrArg NMB_Stage1Source.Run.post tail,?_⟩
  change (NMB_ThreeSnapshots.G x alloc0 alloc1 alloc2).events.map NMB_Stage1Source.Event.snapshot ++
   (NMB_TypedParent.continuation ops p d pair.1 ⟨pair.2,none⟩).events.map eraseEvent = _
  exact congrArg (fun es=>(NMB_ThreeSnapshots.G x alloc0 alloc1 alloc2).events.map
   NMB_Stage1Source.Event.snapshot ++ es) (congrArg NMB_Stage1Source.Run.events tail)
#print source
#print axioms copy
#print axioms continuation
#print axioms source
end NMB_TypedParentFold
