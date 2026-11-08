import PV_LIB_SPEC_HookKinds14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_SpawnHooks14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_HookKinds14 PV_LIB_SPEC_ThreadWords12
local instance : DecidableEq Data := Classical.decEq _
/-- Opaque Unique<u8> and UsizeNoHighBit use numeric pointer/cap facets;
the surrounding RawVec fields are exact frozen source types. There is no
allocation on the empty-list branch, and no element bytes are invented. -/
def hooks : Data := PV_THR2_KeyValues.pack hooksKind [PV_THR2_KeyValues.pack noneKind []]
def raw : Data := PV_THR2_KeyValues.pack rawKind
  [PV_THR2_KeyValues.pack innerKind [.number 8,.number 0,.null],
   PV_THR2_KeyValues.pack markerKind []]
def value : Data := PV_THR2_KeyValues.pack childKind
  [hooks,PV_THR2_KeyValues.pack vectorKind [raw,.number 0]]

/-- The adopted17c7ec/17c814 take/clone/set sequence restores empty TLS.
17c943..17c981 writes cap0,ptr8,len0,hooksNone0 to r15. At caller e056c,
r15=rsp+0x38. Unknown/nonempty/uninitialized TLS stays an explicit gap.
This function accepts native frame DATA, not a chosen memory transformer. -/
def empty (slot : Nat) (w : OWNER) : Option Unit := do
  let first ← read w slot
  if first.val=0 ∧ w.world.memory (slot+8)=some 1 then some () else none

def thread (p : Parameters) (c : Config) (w : OWNER) (args : List Data) : Option Nat := do
  let [reference] := args | none
  let address ← (runtime p).carrier.dereference w reference
  let v ← readAddress (runtime p).carrier c.store address
  let ptr ← PV_THR2_OwnInitPointerCodec.decode v
  if ptr.val=0 then none else some ptr.val

def result (native : PV_LIB_SPEC_PhysicalStack12.Frame) (w : OWNER)
    (r : Reply OWNER Event Data) : Reply OWNER Event Data :=
  ⟨.returned (.ok value),PV_LIB_SPEC_PhysicalStack12.installDefault native w,r.events⟩

def reply (native : PV_LIB_SPEC_PhysicalStack12.Frame) (slot : Nat)
    (p : Parameters) (c : Config) (w : OWNER) (args : List Data)
    (r : Reply OWNER Event Data) : Option (Reply OWNER Event Data) :=
  match r.answer with
  | .returned (.ok _) => do
    let _ ← thread p c w args
    let _ ← empty slot w
    pure (result native w r)
  | _ => some r

/-- Separate no_hooks=true branch, sourced by exact453. It uses the same
returned value and the direct e0550/e0559/e0565 stores, with no TLS read. -/
def defaultReply (native : PV_LIB_SPEC_PhysicalStack12.Frame) (w : OWNER)
    (r : Reply OWNER Event Data) : Reply OWNER Event Data :=
  match r.answer with
  | .returned (.ok _) => result native w r
  | _ => r

theorem fields (p : Parameters) :
    (runtime p).carrier.field value 0 = some hooks ∧
    (runtime p).carrier.field value 1 = some (PV_THR2_KeyValues.pack vectorKind [raw,.number 0]) ∧
    (runtime p).carrier.field hooks 0 = some (PV_THR2_KeyValues.pack noneKind []) ∧
    (runtime p).control.variant (PV_THR2_KeyValues.pack noneKind []) = some 0 :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem empty_initialized (w : OWNER) (slot : Nat)
    (flag : (write w slot 0).world.memory (slot+8) = some 1) :
    empty slot (write w slot 0) = some () := by
  unfold empty
  rw [read_written w slot (⟨0,by decide⟩ : Pointer)]
  exact if_pos ⟨rfl,flag⟩

theorem output (native : PV_LIB_SPEC_PhysicalStack12.Frame) (w : OWNER)
    (r : Reply OWNER Event Data) (i : Nat) (bound : i<32) :
    ∃ v, PV_LIB_SPEC_PhysicalStack12.defaultHooks i = some v ∧
      (result native w r).world.world.memory (native.rsp+0x38+i) = v :=
  PV_LIB_SPEC_PhysicalStack12.default_snapshot native w i bound

theorem other (native : PV_LIB_SPEC_PhysicalStack12.Frame) (slot : Nat)
    (p : Parameters) (c : Config) (w : OWNER) (args : List Data)
    (r : Reply OWNER Event Data) (h : ∀ v, r.answer ≠ .returned (.ok v)) :
    reply native slot p c w args r = some r := by
  cases a : r.answer with
  | pending => simp only [reply,a]
  | fault f => simp only [reply,a]
  | returned out => cases out with
    | ok v => exact False.elim (h v a)
    | fail e => simp only [reply,a]
    | div => simp only [reply,a]

#print axioms hooks
#print axioms raw
#print axioms value
#print axioms empty
#print axioms thread
#print axioms result
#print axioms reply
#print axioms defaultReply
#print axioms fields
#print axioms empty_initialized
#print axioms output
#print axioms other
end PV_LIB_SPEC_SpawnHooks14
