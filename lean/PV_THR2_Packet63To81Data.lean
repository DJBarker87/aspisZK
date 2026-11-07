import PV_THR2_PacketChild63Store
import PV_THR2_PacketChild70Store
import PV_THR2_PacketMetadata64Store
import PV_THR2_PacketMetadata71Store
import PV_THR2_PacketMetadata76Frame
import PV_THR2_PacketMetadata77Store
import PV_THR2_PacketReturnedStoreFrame
set_option autoImplicit false
namespace PV_THR2_Packet63To81Data
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Complete source continuation stores. Counter and metadata replies remain
arbitrary values; no store cell or activation counter is projected away. -/
def moved63 (s : Store Data) (a : Nat) := write s ⟨a,24,[]⟩ none
def store64 (s : Store Data) (a : Nat) (argument counter : Data) :=
  PV_THR2_StaticReply.returnedStore (moved63 s a) a [argument] 23 counter
def store70 (s : Store Data) (a : Nat) (argument counter captured : Data) :=
  PV_THR2_Spawn361MetadataMove64Reached.prepared (store64 s a argument counter) a captured
def moved70 (s : Store Data) (a : Nat) (argument counter captured : Data) :=
  write (store70 s a argument counter captured) ⟨a,26,[]⟩ none
def store71 (s : Store Data) (a : Nat) (argument counter captured metadata : Data) :=
  PV_THR2_StaticReply.returnedStore (moved70 s a argument counter captured) a [captured] 25 metadata
def store76 (s : Store Data) (a : Nat) (argument counter captured metadata : Data) :=
  PV_THR2_Spawn361MetadataStorage71Reached.prepared (store71 s a argument counter captured metadata) a
def store77 (s : Store Data) (a : Nat) (argument counter captured metadata aggregate : Data) :=
  PV_THR2_PacketMetadata76Frame.prepared (store76 s a argument counter captured metadata) a aggregate
def store81 (s : Store Data) (a : Nat) (argument counter captured metadata aggregate : Data) :=
  PV_THR2_Spawn361MetadataReference77Reached.prepared (store77 s a argument counter captured metadata aggregate) a
/-- At the actual13323 call both opaque calls have consumed one activation. -/
theorem next (s : Store Data) (a : Nat) (argument counter captured metadata aggregate : Data) :
    (store81 s a argument counter captured metadata aggregate).nextActivation = s.nextActivation+2 := rfl
/-- Derived by the source write at13134, not a new receiver premise. -/
theorem reference (s : Store Data) (a : Nat) (argument counter captured metadata aggregate : Data) :
    (store81 s a argument counter captured metadata aggregate).cells ⟨a,30,[]⟩ =
      some (PV_STX2_TypedReferences.reference ⟨a,17,[]⟩ .null) := by
  simp [store81,PV_THR2_Spawn361MetadataReference77Reached.prepared,write]
/-- Source17 survives all metadata work on the actual store. -/
theorem arc (s : Store Data) (a : Nat) (argument counter captured metadata aggregate : Data)
    (fresh : a < s.nextActivation) :
    (store81 s a argument counter captured metadata aggregate).cells ⟨a,17,[]⟩ = s.cells ⟨a,17,[]⟩ := by
  have n0 : a ≠ s.nextActivation := Nat.ne_of_lt fresh
  have n1 : a ≠ s.nextActivation+1 := by omega
  simp [store81,store77,store76,store71,moved70,store70,store64,moved63,
    PV_THR2_PacketMetadata76Frame.prepared,PV_THR2_Spawn361MetadataReference77Reached.prepared,
    PV_THR2_Spawn361MetadataStorage71Reached.prepared,PV_THR2_Spawn361MetadataMove64Reached.prepared,
    PV_THR2_StaticReply.returnedStore,PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,write,n0,n1]
/-- Foreign ArcInner fields persist; freshness excludes both opaque activations. -/
theorem backing (s : Store Data) (a : Nat) (argument counter captured metadata aggregate : Data)
    (p : Address) (older : p.activation < s.nextActivation) (other : p.activation ≠ a) :
    (store81 s a argument counter captured metadata aggregate).cells p = s.cells p := by
  have ne : ∀ i, p ≠ (⟨a,i,[]⟩ : Address) := fun i h => other (congrArg Address.activation h)
  have n0 : ∀ i, p ≠ (⟨s.nextActivation,i,[]⟩ : Address) := fun i h => (Nat.ne_of_lt older) (congrArg Address.activation h)
  have n1 : ∀ i, p ≠ (⟨s.nextActivation+1,i,[]⟩ : Address) := by
    intro i h
    have bad := congrArg Address.activation h
    change p.activation = s.nextActivation+1 at bad
    omega
  simp [store81,store77,store76,store71,moved70,store70,store64,moved63,
    PV_THR2_PacketMetadata76Frame.prepared,PV_THR2_Spawn361MetadataReference77Reached.prepared,
    PV_THR2_Spawn361MetadataStorage71Reached.prepared,PV_THR2_Spawn361MetadataMove64Reached.prepared,
    PV_THR2_StaticReply.returnedStore,PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,write,ne,n0,n1]
#print axioms next
#print axioms reference
#print axioms arc
#print axioms backing
end PV_THR2_Packet63To81Data
