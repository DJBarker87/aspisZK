import NLF_WrapperLaws
import AdapterRwRuntimeAdmission
set_option autoImplicit false
namespace NLF_Admission
open NLF_RefCell NLF_SdkModel
open AspisR1
/-- Initial std interpretation; token ledger starts empty. Metadata is copied
from the admitted records, with both Rc cell identities taken from the SAME heap.
Lamport payload interpretation is separate from byte payload interpretation. -/
def initial {F : Type} (h : S2Trust.Heap F) (records : Nat → Account)
    (bytes : Nat → List UInt8) (money : Nat → Nat) : State :=
  ⟨(fun a => {records a with data := (h.accounts a).1, lamports := (h.accounts a).2}),
    (fun i => ⟨⟨bytes i,money i⟩,[],none⟩)⟩

theorem initial_valid {F : Type} (h : S2Trust.Heap F) (records : Nat → Account)
    (bytes : Nat → List UInt8) (money : Nat → Nat) (i : Nat) :
    Valid ((initial h records bytes money).cells i) := by simp [initial, Valid]

theorem initial_counter {F : Type} (h : S2Trust.Heap F) (records : Nat → Account)
    (bytes : Nat → List UInt8) (money : Nat → Nat) (keys : Nat → List UInt8) (n a : Nat)
    (runtime : AdapterRw.RuntimeEntrypointAdmission h keys n) (ha : a < n) :
    flag ((initial h records bytes money).cells (h.accounts a).1) = h.counter (h.accounts a).1 ∧
    h.ownerLive a = true := by
  simp [initial, flag, runtime.counterZero a ha, runtime.liveAccount a ha]

theorem different_keys {F : Type} (h : S2Trust.Heap F) (keys : Nat → List UInt8)
    (n a b : Nat) (runtime : AdapterRw.RuntimeEntrypointAdmission h keys n)
    (ha : a < n) (hb : b < n) (different : keys a ≠ keys b) :
    (h.accounts a).1 ≠ (h.accounts b).1 :=
  AdapterRw.distinct_keys_distinct_cells runtime ha hb different

theorem same_keys {F : Type} (h : S2Trust.Heap F) (keys : Nat → List UInt8)
    (n a b : Nat) (runtime : AdapterRw.RuntimeEntrypointAdmission h keys n)
    (ha : a < n) (hb : b < n) (same : keys a = keys b) :
    (h.accounts a).1 = (h.accounts b).1 := runtime.duplicateKeysShareCell a b ha hb same

theorem aliases_exactly {F : Type} (h : S2Trust.Heap F) (keys : Nat → List UInt8)
    (n a b : Nat) (runtime : AdapterRw.RuntimeEntrypointAdmission h keys n)
    (ha : a < n) (hb : b < n) :
    ((h.accounts a).1 = (h.accounts b).1 ↔ keys a = keys b) :=
  ⟨runtime.sharedCellsOnlyEqualKeys a b ha hb, runtime.duplicateKeysShareCell a b ha hb⟩

#print axioms initial_valid
#print axioms initial_counter
#print axioms different_keys
#print axioms same_keys
#print axioms aliases_exactly
end NLF_Admission
