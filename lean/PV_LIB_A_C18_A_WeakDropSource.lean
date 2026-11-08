import PV_LIB_A_DropStoreV2
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_WeakDropSource
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_THR2_SourceStoreLibrary PV_LIB_A_StorePrimitiveV2

/-- Separate the decrement from final deallocation. A pending native answer
must not cause another decrement or prematurely destroy the source block. -/
inductive Tail where
  | done
  | deallocate (block : Address)

structure Started where
  store : Store Data
  tail : Tail

def pointer {W : Type} (C : Carrier W Data) (args : List Data)
    (s : Store Data) (w : W) : Option Data := do
  match args with
  | [reference] =>
    let (_,weak) ← receiver C s w reference
    let nonNull ← C.field weak 0
    C.field nonNull 0
  | _ => none

/-- Pinned sync.rs3468–3494: dangling usize::MAX returns before any access;
otherwise weak.fetch_sub(1,Release), then (only old=1) acquire/deallocation.
The exact raw-word codec is OwnInitPointerCodec; it does not truncate words.
OWNER-only pointer backing is still a separate unsupplied binding. -/
def PV_THR2_LibrarySemantics_WeakDropBegin683 {W : Type} (C : Carrier W Data)
    (args : List Data) (s : Store Data) (w : W) : Option Started := do
  let ptr ← pointer C args s w
  match ptr with
  | .number n => if n = modulus-1 then pure ⟨s,.done⟩ else allocated ptr
  | _ => allocated ptr
where
  allocated (ptr : Data) : Option Started := do
    let p ← C.dereference w ptr
    let count : Address := {p with fields := p.fields ++ [1,0,0]}
    let n ← numberAt C s count
    let post ← writeAddress C s count (some (.number ((n+modulus-1)%modulus)))
    pure ⟨post,if n = 1 then .deallocate p else .done⟩

/-- The source-block lifetime ends at the successful deallocation completion,
not at its pending request. The original full native answer/world/events must
still be delivered by the machine, never replaced by this source projection.
This is a SOURCE lifetime model; OWNER allocator/registry adequacy is separate. -/
def finish {W E : Type} (C : Carrier W Data) (tail : Tail)
    (s : Store Data) (r : Reply W E Data) : Option (Store Data) :=
  match tail,r.answer with
  | .deallocate p,.returned (.ok _) => writeAddress C s p none
  | _,_ => some s

theorem pending {W E : Type} (C : Carrier W Data) (tail : Tail)
    (s : Store Data) (w : W) (es : List E) :
    finish C tail s ⟨.pending,w,es⟩ = some s := by
  cases tail <;> rfl

theorem failure {W E : Type} (C : Carrier W Data) (tail : Tail)
    (s : Store Data) (w : W) (es : List E) (error : Aeneas.Std.Error) :
    finish C tail s ⟨.returned (.fail error),w,es⟩ = some s := by
  cases tail <;> rfl

theorem fault {W E : Type} (C : Carrier W Data) (tail : Tail)
    (s : Store Data) (w : W) (es : List E) (f : Fault) :
    finish C tail s ⟨.fault f,w,es⟩ = some s := by
  cases tail <;> rfl

theorem last_deallocate {W E : Type} (C : Carrier W Data)
    (s : Store Data) (p : Address) (w : W) (es : List E) (v : Data) :
    finish C (.deallocate p) s ⟨.returned (.ok v),w,es⟩ = writeAddress C s p none := rfl

theorem dangling {W : Type} (C : Carrier W Data) (args : List Data)
    (s : Store Data) (w : W)
    (raw : pointer C args s w = some (.number (modulus-1))) :
    PV_THR2_LibrarySemantics_WeakDropBegin683 C args s w = some ⟨s,.done⟩ := by
  unfold PV_THR2_LibrarySemantics_WeakDropBegin683
  rw [raw]
  change (if modulus-1 = modulus-1 then some (⟨s,.done⟩ : Started)
    else PV_THR2_LibrarySemantics_WeakDropBegin683.allocated C s w (.number (modulus-1))) = _
  rw [if_pos rfl]

#print axioms pointer
#print axioms PV_THR2_LibrarySemantics_WeakDropBegin683
#print axioms finish
#print axioms pending
#print axioms failure
#print axioms fault
#print axioms last_deallocate
#print axioms dangling
end PV_LIB_A_WeakDropSource
