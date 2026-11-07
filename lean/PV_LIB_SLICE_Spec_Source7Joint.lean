import PV_LIB_SLICE_Spec_f0
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SLICE_Spec_Source7Joint
open scoped Classical
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OWNER PV_EVHB_RawVecOwner
open PV_LIB_SLICE_Statements
open PV_STX2_Source7EntryOwned

/-- Concrete legal empty-column fixture; not a successful allocation premise. -/
def header : Header := ⟨4,0,0,⟨4,._Align1Shl2⟩,true⟩
def state : OWNER :=
  {world := {allocator := ⟨{},fun _ => none⟩
             frame := ⟨(),fun id => if id = 0 then some header else none⟩
             live := fun _ => false
             memory := fun _ => none
             history := []
             allocCalls := 0,reallocCalls := 0,deallocCalls := 0
             successfulAlloc := 0,successfulRealloc := 0,drops := 0}
   next := 1
   places := fun p => if p.activation = 0 then some 0 else none}
def foundation : Foundation := ⟨⟨List.replicate 16 ⟨[],by simp⟩,by simp⟩⟩

theorem values_empty (i : Fin foundation.c1.val.length) : values foundation i = [] := by
  change ((List.replicate 16 (⟨[],by simp⟩ : alloc.vec.Vec PV_OWN2_Codec.M31))[i.val]).val = []
  rw [List.getElem_replicate]
theorem ids : PV_STX2_OwnerWellFormed.OwnerWellFormed state := by
  intro p id found
  change (if p.activation = 0 then some 0 else none) = some id at found
  split at found
  · cases found; decide
  · cases found

theorem wf (counter : Nat) (positive : 0 < counter) :
    PV_STX2_OwnerAllocationReferenceValid.OwnerWellFormed state counter := by
  refine ⟨⟨⟨ids,?_⟩,?_⟩,?_⟩
  · intro p id found
    change (if p.activation = 0 then some 0 else none) = some id at found
    split at found
    · next equal => simpa only [equal] using positive
    · cases found
  · intro p a h; cases h
  · intro p a h; cases h

theorem typed : PV_OWN2_Codec.TypedMemory 4 PV_OWN2_Codec.decodeM31 state ⟨⟨0,[4]⟩,[]⟩ := by
  constructor
  · exact ⟨0,header,rfl,Or.inr ⟨rfl,rfl⟩,rfl,by decide⟩
  · intro id h found
    change some (0,header) = some (id,h) at found
    cases found
    exact ⟨rfl,by intro i bound; simp at bound⟩

theorem owned : Source7EntryOwned state foundation := by
  intro i
  refine ⟨⟨0,[4]⟩,0,header,rfl,rfl,?_,rfl,?_⟩
  · rw [values_empty]; exact Nat.zero_le _
  · simpa only [values_empty] using typed

theorem selected_header (i : Fin foundation.c1.val.length) :
    PV_STX2_Source7EntrySelection.header owned i = header := by
  have h := (PV_STX2_Source7EntrySelection.selected owned i).2.1
  change (if PV_STX2_Source7EntrySelection.identity owned i = 0 then some header else none) = some _ at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

def indexed : PV_STX2_Source7EntryOwnedIndexed.Source7EntryOwned''' state foundation :=
  ⟨owned,ids,by
    intro i
    have selected := (PV_STX2_Source7EntrySelection.selected owned i).1
    change (if (PV_STX2_Source7EntrySelection.place owned i).activation = 0 then some 0 else none) = _ at selected
    change some 0 = _
    rw [PV_STX2_Source7EntrySelection.selected owned i |>.1]
    have slot := (PV_STX2_Source7EntrySelection.selected owned i).2.1
    change (if PV_STX2_Source7EntrySelection.identity owned i = 0 then some header else none) = some _ at slot
    split at slot
    · next zero => rw [zero]
    · cases slot⟩

def valid : PV_STX2_Source7EntryReferenceValid.Source7EntryOwned''''' state foundation :=
  ⟨⟨indexed,by intro i; rw [selected_header]; decide⟩,
    by intro i; rw [selected_header]; decide,
    by intro i; rw [selected_header,values_empty]; decide⟩

/-- Explicit source carrier primitives. Full semantics adequacy is not a
premise of these statement declarations and is not claimed by this fixture. -/
def base : Carrier PV_STX_World.World Data :=
  {global := fun _ _ => none
   constant := fun v => some v
   dereference := fun _ _ => none
   field := fun v i => match v with | .array xs => xs[i]? | _ => none
   replaceField := fun _ _ _ => none
   metadata := fun _ => none
   reference := PV_STX2_TypedReferences.reference
   aggregate := fun tag vs => some (PV_STX2_Aggregates.pack tag vs)
   unary := fun _ v => some v
   binary := fun _ _ _ => none
   nullary := fun _ _ => none
   truth := fun _ => none
   matchesKey := fun _ _ => false}
def ctrl : Control := ⟨fun _ => none,fun _ _ _ => none⟩
def external : PV_W5_NoAllocShim.External := fun _ w => ⟨.pending,w,[]⟩
def backend : PV_W5_NativeFrame.Backend := fun _ w => ⟨.pending,w,[]⟩
def handler := PV_STX2_Source7QPreludeWorld.handler external
  (PV_STX2_Source7QRuntimePartsReply.handler (PV_STX2_Source7QUniformResourceHandler.lift backend))
def machine : Machine :=
  ⟨PV_STX2_ToVecZeroCallCarrier.C base ctrl handler,
    PV_STX2_ToVecZeroCallCarrier.control ctrl,
    PV_STX2_Source7QAllocationDispatch.dispatch PV_STX2_SlicePrograms.dispatch,handler⟩
def environment (r : Resources) (enc : Encode) : Environment :=
  ⟨fun q => PV_EVHB_AttemptAccounting.primitive r enc q.identity
      (.malloc (match q.arguments with | .number n :: _ => n | _ => 0)) q.before,
    fun q => ⟨.pending,q.before,[]⟩⟩
theorem machine_spec (r : Resources) (enc : Encode) :
    MachineSpec machine base ctrl external backend r enc (environment r enc) := by
  refine ⟨⟨rfl,rfl,rfl,rfl,?_⟩,?_⟩
  · change machine.carrier.unary PV_STX2_ToVecZeroPrepare.cast (.number 4) = some (.number 4)
    simp [machine,
      PV_STX2_ToVecZeroCallCarrier.C,
      PV_STX2_ToVecZeroCapCarrier.install,
      PV_STX2_SliceAggregateExtension.extend,
      PV_STX2_ToVecZeroCallCarrier.original,
      PV_STX2_Source7QUniformReturnCompatibility.C,
      PV_STX2_Source7QUniformHeaderCarrier.carrier,
      PV_STX2_Source7QOriginalAllocatedCarrier.carrier,
      PV_STX2_Source7QOriginalLayoutCarrier.layoutCarrier,
      PV_STX2_Source7QOriginalScalarCarrier.uniform,
      PV_STX2_Source7QOriginalScalar.carrier,
      PV_STX2_Source7ConstructorEntry.carrier,
      PV_STX2_Source7ReachedConstructor.carrier,
      PV_STX2_Source7ReachedConstructor.staticBase,
      PV_STX2_SliceClonePointers.carrier,
      PV_STX2_SliceOutputEntry.carrier,
      PV_STX2_SliceOutputInterpretation.arrayWrites,
      PV_STX2_SliceClonePointers.pointers,
      PV_STX2_SliceCompleteAggregates.carrier,
      PV_STX2_SliceLoopGuard.comparisons,
      PV_STX2_SliceColumnPointer.one,
      PV_STX2_SliceArrayInterpretation.carrier,
      PV_STX2_SliceTypedEntry.carrier,
      PV_STX2_Aggregates.carrier,
      PV_STX2_TypedReferences.carrier,
      PV_STX2_LengthBranch.carrier,
      PV_STX2_Uc7Guards.carrier,
      PV_STX2_Pinned.withUbChecks,
      PV_STX2_Source7LayoutGlobals.carrier,
      PV_STX2_Source7LayoutScalars.carrier,
      PV_STX2_Source7QOriginalScalar.primitives,
      PV_STX2_Source7QUniformInstalledCarrier.B,
      PV_STX2_Source7CapacityLimit.primitives,
      PV_STX2_Source7AllocationRuntimeBranch.keys,
      PV_STX2_Source7QOriginalAllocatedUnary.primitives,
      PV_STX2_Source7QUniformBackendCarrier.lift,
      PV_STX2_Source7QUniformReturnInstalled.primitives,
      PV_STX2_Source7QF31Capacity.carrier,
      PV_STX2_Source7QF31Assert.scalars,
      PV_STX2_Source7QRuntimeValues.carrier,
      PV_STX2_Source7QLayoutValues.carrier,
      base,
      PV_STX2_ToVecZeroPrepare.cast,
      PV_STX2_Source7CtorF35.node76,
      PV_STX2_SliceArrayInterpretation.isRawCast,PV_STX2_SliceClonePointers.isTransmute,
      PV_STX2_SliceToVecBranch.comparisons,PV_STX2_Source7CapacityScalars.carrier,
      PV_STX2_Source7QF31Capacity.cast,PV_STX2_Source7QRuntimeValues.partsCast,
      PV_STX2_Source7QRuntimeValues.scalarCast,PV_STX2_Source7QRuntimeValues.thinCast,
      PV_STX2_Source7CapacityScalars.isCast,PV_STX2_Source7CtorF31.node33]
  · intro id bytes w; rfl

/-- SAME entry selections as the complete f0 Pre, including ghost place/id. -/
def source (i : Fin 16) : Source :=
  let j : Fin foundation.c1.val.length := ⟨i.val,by simpa [foundation] using i.isLt⟩
  ⟨⟨0,0,[0,i.val]⟩,
    ⟨PV_STX2_Source7EntrySelection.place owned j,values foundation j⟩,
    PV_STX2_Source7EntrySelection.identity owned j,
    PV_STX2_Source7EntrySelection.header owned j⟩
def root : Data := PV_STX2_Aggregates.pack PV_STX2_AggregateKinds.source7Kind
  [.array (List.ofFn (fun i => vector (source i).header))]
def store : Store Data := ⟨fun p => if p = ⟨0,0,[]⟩ then some root else none,20⟩
def entry : PV_LIB_SLICE_Spec_f0.Entry :=
  {store := store,parents := [],owner := state,prior := [],suspended := []
   columns := source,arrayAddress := ⟨0,0,[0]⟩,capture := ⟨1,0,[]⟩,buffer := ⟨2,0,[]⟩,
   index := ⟨0,by decide⟩,foundationAddress := ⟨0,0,[]⟩,foundation := foundation}

theorem source_valid (i : Fin 16) :
    (source i).Valid machine (PV_LIB_SLICE_Spec_f0.start entry) entry.toArrayEntry.toEntry := by
  refine ⟨?_,?_,?_,?_⟩
  · exact PV_STX2_ToVecCallReferenceEntry.column valid _ _ (wf 21 (by decide))
  · change readAddress machine.carrier (PV_LIB_SLICE_Spec_f0.start entry).store ⟨0,0,[0,i.val]⟩ = _
    have root_cell : (PV_LIB_SLICE_Spec_f0.start entry).store.cells ⟨0,0,[]⟩ = some root := by
      simp [PV_LIB_SLICE_Spec_f0.start,PV_LIB_SLICE_Statements.start,enter,entry,
        PV_STX2_Native.arguments,write,store]
    simp only [readAddress,readFields,root_cell,Option.bind_some]
    simp [machine,
      PV_STX2_ToVecZeroCallCarrier.C,
      PV_STX2_ToVecZeroCapCarrier.install,
      PV_STX2_SliceAggregateExtension.extend,
      PV_STX2_ToVecZeroCallCarrier.original,
      PV_STX2_Source7QUniformReturnCompatibility.C,
      PV_STX2_Source7QUniformHeaderCarrier.carrier,
      PV_STX2_Source7QOriginalAllocatedCarrier.carrier,
      PV_STX2_Source7QOriginalLayoutCarrier.layoutCarrier,
      PV_STX2_Source7QOriginalScalarCarrier.uniform,
      PV_STX2_Source7QOriginalScalar.carrier,
      PV_STX2_Source7ConstructorEntry.carrier,
      PV_STX2_Source7ReachedConstructor.carrier,
      PV_STX2_Source7ReachedConstructor.staticBase,
      PV_STX2_SliceClonePointers.carrier,
      PV_STX2_SliceOutputEntry.carrier,
      PV_STX2_SliceOutputInterpretation.arrayWrites,
      PV_STX2_SliceClonePointers.pointers,
      PV_STX2_SliceCompleteAggregates.carrier,
      PV_STX2_SliceLoopGuard.comparisons,
      PV_STX2_SliceColumnPointer.one,
      PV_STX2_SliceArrayInterpretation.carrier,
      PV_STX2_SliceTypedEntry.carrier,
      PV_STX2_Aggregates.carrier,
      PV_STX2_TypedReferences.carrier,
      PV_STX2_LengthBranch.carrier,
      PV_STX2_Uc7Guards.carrier,
      PV_STX2_Pinned.withUbChecks,
      PV_STX2_Source7LayoutGlobals.carrier,
      PV_STX2_Source7LayoutScalars.carrier,
      PV_STX2_Source7QOriginalScalar.primitives,
      PV_STX2_Source7QUniformInstalledCarrier.B,
      PV_STX2_Source7CapacityLimit.primitives,
      PV_STX2_Source7AllocationRuntimeBranch.keys,
      PV_STX2_Source7QOriginalAllocatedUnary.primitives,
      PV_STX2_Source7QUniformBackendCarrier.lift,
      PV_STX2_Source7QUniformReturnInstalled.primitives,
      PV_STX2_Source7QF31Capacity.carrier,
      PV_STX2_Source7QF31Assert.scalars,
      PV_STX2_Source7QRuntimeValues.carrier,
      PV_STX2_Source7QLayoutValues.carrier,
      base,
      root,
      PV_STX2_Aggregates.pack,
      PV_STX2_Aggregates.slotValue]
    change (List.ofFn (fun j : Fin 16 => vector (source j).header))[i.val] = vector (source i).header
    rw [List.getElem_ofFn]
  · change 0 < 20; decide
  · change (values foundation _).length < _
    rw [values_empty]; decide

theorem pre : PV_LIB_SLICE_Spec_f0.Pre machine entry := by
  refine ⟨⟨⟨?_,?_,wf 21 (by decide)⟩,?_,?_⟩,valid,?_,rfl,?_,?_⟩
  · exact PV_STX2_LiveNumbering.initial _ _ _
  · intro c hc; cases hc
  · rfl
  · intro i; exact ⟨source_valid i,rfl⟩
  · intro i; exact ⟨rfl,rfl,rfl⟩
  · rfl
  · intro i; rfl

/-- Joint non-emptiness of the full source7 entry and its named machine and
resource-channel premises. No per-column success, Contract or run is assumed.
This is a witness to premises, not a proof of source7 clone correctness. -/
theorem joint (r : Resources) (enc : Encode) :
    ∃ m : Machine, ∃ env : Environment, ∃ e : PV_LIB_SLICE_Spec_f0.Entry,
      MachineSpec m base ctrl external backend r enc env ∧ PV_LIB_SLICE_Spec_f0.Pre m e :=
  ⟨machine,environment r enc,entry,machine_spec r enc,pre⟩
#print axioms wf
#print axioms typed
#print axioms owned
#print axioms valid
#print axioms machine_spec
#print axioms source_valid
#print axioms pre
#print axioms joint
end PV_LIB_SLICE_Spec_Source7Joint
