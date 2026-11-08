import PV_LIB_A_AllocationBacking9
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_WeakOwnerFree9
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_CellSetBegin PV_LIB_A_TypedDestruct

/-- Exact normalized Global type from typed metadata, not the erased marker. -/
def globalType : Data → Bool
  | .object [("Adt",.object [("id",.object [("Adt",.number 1)]),("generics",.object
      [("regions",.array []),("types",.array []),("const_generics",.array []),
       ("trait_refs",.array [])])])] => true
  | _ => false

/-- Global or a source SHARED reference to it, as in drop_slow's weak guard.
A custom allocator is never interpreted as libc free on pointer shape alone. -/
def allocator (C : Carrier OWNER Data) (s : Store Data) (w : OWNER)
    (ty value : Data) : Option Unit := do
  let actual ← if globalType ty then some value else
    match ty with
    | .object [("Ref",.array [_,pointee,.atom "Shared"])] =>
      if globalType pointee then do
        let p ← C.dereference w value
        readAddress C s p
      else none
    | _ => none
  let _ ← PV_LIB_A_AllocatorProvenance.allocatorType actual
  pure ()

/-- The exact683 type arguments and Weak.alloc value, read from the source.
The source reference into the still-live Arc holds the guard's allocator. -/
def weakAllocator (C : Carrier OWNER Data) (c : Config) (w : OWNER)
    (site : SourceSite) : Option Unit := do
  let normalized ← normalize 64 site.callee
  let ptr ← member "Regular" normalized
  let raw ← member "generics" ptr
  let g ← generics raw
  let [_,ty] := g.types | none
  let [reference] := site.arguments | none
  let (_,weak) ← receiver C c.store w reference
  let value ← C.field weak 1
  allocator C c.store w ty value

/-- Map the allocator's actual full reply; only its unit success payload gets
the source unit representation. No world/event/status branch is discarded. -/
def reply (unit : Data) (r : Reply OWNER PV_RJ4IDB.NativeEvent Unit) :
    Reply OWNER PV_RJ4IDB.NativeEvent Data :=
  ⟨match r.answer with
   | .returned (.ok _) => .returned (.ok unit)
   | .returned (.fail e) => .returned (.fail e)
   | .returned .div => .returned .div
   | .fault f => .fault f
   | .pending => .pending,r.world,r.events⟩

def gap (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent)
    (stack : List Config) : SourceState :=
  ⟨⟨⟨.undefined none c.store,w,es⟩,stack⟩,none⟩

/-- The source root is cleared only by a successful free primitive. The OWNER
primitive ends the corresponding physical allocator lifetime, retains arbitrary
resource failures/pending, and never clears the underlying byte map. -/
def poll (C : Carrier OWNER Data) (resources : Resources) (encode : Encode)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : SourceSite) (p : Address) : SourceState :=
  match weakAllocator C c w site,C.aggregate PV_LIB_A_GenericDropMachine.unitTag [] with
  | some (),some unit =>
    match PV_LIB_A_AllocationBacking9.deallocate resources encode w p with
    | none => gap c w es stack
    | some r => sourceReceive C c es stack site (.deallocate p) (reply unit r)
  | _,_ => gap c w es stack

/-- A new resource-aware last-Weak extension. Nonlast/dangling paths retain the
existing full native replies. Applied last-free phases retry without repeating
the weak decrement. Missing allocator/backing stays an explicit model gap. -/
def step (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : SourceState) : SourceState :=
  let programs := v2ProvenancePrograms P
  let carrier := PV_LIB_A_UnwindMatch.carrier C K
  match s.applied,s.base.current.status with
  | some (site,.deallocate p),.running c =>
    match site.action with
    | .weakDrop683 => poll carrier resources encode c s.base.current.world
        s.base.current.events s.base.suspended site p
    | _ => v2ProvenanceStep C K P resources encode H values s
  | none,.running c =>
    match sourceSelect programs c with
    | some site => match site.action with
      | .weakDrop683 =>
        match PV_LIB_A_WeakDropSource.PV_THR2_LibrarySemantics_WeakDropBegin683
            carrier site.arguments c.store s.base.current.world with
        | some ⟨post,.deallocate p⟩ => poll carrier resources encode {c with store := post}
            s.base.current.world s.base.current.events s.base.suspended site p
        | _ => v2ProvenanceStep C K P resources encode H values s
      | _ => v2ProvenanceStep C K P resources encode H values s
    | none => v2ProvenanceStep C K P resources encode H values s
  | _,_ => v2ProvenanceStep C K P resources encode H values s

theorem pending_reply (unit : Data) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) :
    reply unit ⟨.pending,w,es⟩ = ⟨.pending,w,es⟩ := rfl

theorem retry (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : SourceSite) (p : Address) (weak : site.action = .weakDrop683) :
    step C K P resources encode H values ⟨⟨⟨.running c,w,es⟩,stack⟩,some (site,.deallocate p)⟩ =
      poll (PV_LIB_A_UnwindMatch.carrier C K) resources encode c w es stack site p := by
  simp only [step,weak]

/-- The response's post-world and events are preserved on ALL reply branches. -/
theorem reply_effects (unit : Data) (r : Reply OWNER PV_RJ4IDB.NativeEvent Unit) :
    (reply unit r).world = r.world ∧ (reply unit r).events = r.events := ⟨rfl,rfl⟩

#print axioms globalType
#print axioms allocator
#print axioms weakAllocator
#print axioms reply
#print axioms gap
#print axioms poll
#print axioms step
#print axioms pending_reply
#print axioms retry
#print axioms reply_effects
end PV_LIB_A_WeakOwnerFree9
