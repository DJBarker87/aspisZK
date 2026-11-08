import PV_LIB_A_ScopeStoreV2
import PV_THR2_OwnInitExactReturnedCases
import PV_THR2_ScopeData
import PV_THR2_Packet124Aggregate13
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ScopePayloadShape14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
abbrev carrier := PV_THR2_OwnInitExactReturnedCases.carrier

def atomic (atomicKind cellKind : Data) (n : Nat) :=
  PV_THR2_KeyValues.pack atomicKind [PV_THR2_KeyValues.pack cellKind [.number n]]
def payload (atomicKind cellKind thread panicked : Data) (n : Nat) :=
  PV_THR2_ScopeData.value (atomic atomicKind cellKind n) thread panicked
def inner (atomicKind cellKind strong weak thread panicked : Data) (n : Nat) :=
  PV_THR2_KeyValues.pack PV_THR2_Packet124Aggregate13.source.2.2.1
    [strong,weak,payload atomicKind cellKind thread panicked n]
def root (a slot : Nat) : Address := ⟨a,slot,[]⟩
def count (a slot : Nat) : Address := ⟨a,slot,[2,0,0,0]⟩
def stored (s : Store Data) (a slot : Nat)
    (atomicKind cellKind strong weak thread panicked : Data) (n : Nat) :=
  write s (root a slot) (some (inner atomicKind cellKind strong weak thread panicked n))

theorem reference (C : Carrier OWNER Data) (b : Bool) (w : OWNER) (a slot : Nat) :
    (carrier C b).dereference w (PV_STX2_TypedReferences.reference ⟨a,slot,[2]⟩ .null) = some ⟨a,slot,[2]⟩ := by
  rfl


/-- Read precisely the counter inside the actual ScopeData field order. Native
constructor tags are parameters; all field values and source tags are retained. -/
theorem read_count (C : Carrier OWNER Data) (b : Bool) (s : Store Data) (a slot : Nat)
    (atomicKind cellKind strong weak thread panicked : Data) (n : Nat) :
    readAddress (carrier C b) (stored s a slot atomicKind cellKind strong weak thread panicked n)
      (count a slot) = some (.number n) := by
  unfold readAddress stored count root
  rw [write_same]
  rfl

theorem replace_count (C : Carrier OWNER Data) (b : Bool)
    (atomicKind cellKind strong weak thread panicked : Data) (n m : Nat) :
    replaceFields (carrier C b) [2,0,0,0] (some (.number m))
      (inner atomicKind cellKind strong weak thread panicked n) =
      some (inner atomicKind cellKind strong weak thread panicked m) := rfl

theorem overwrite (s : Store Data) (p : Address) (x y : Option Data) :
    write (write s p x) p y = write s p y := by
  cases s with
  | mk cells counter =>
    change Store.mk _ counter = Store.mk _ counter
    congr 1
    funext q
    by_cases eq : q = p <;> simp [write,eq]

/-- Symbolic source-cell update. No allocation image or native world is defined. -/
theorem write_count (C : Carrier OWNER Data) (b : Bool) (s : Store Data) (a slot : Nat)
    (atomicKind cellKind strong weak thread panicked : Data) (n m : Nat) :
    writeAddress (carrier C b) (stored s a slot atomicKind cellKind strong weak thread panicked n)
      (count a slot) (some (.number m)) =
      some (stored s a slot atomicKind cellKind strong weak thread panicked m) := by
  simp [writeAddress,count,stored,root,replace_count,write]
  funext q
  by_cases h : q = (⟨a,slot,[]⟩ : Address) <;> simp [h]

#print axioms reference
#print axioms read_count
#print axioms replace_count
#print axioms overwrite
#print axioms write_count
end PV_LIB_A_ScopePayloadShape14
