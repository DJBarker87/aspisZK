import PV_THR2_OwnInitFieldCodec
import PV_OWN2_ConstructorSuccess
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OwnInitAllocationReply
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_OWN2_Codec
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_EVHB_RawVecOwner
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
An allocation-child reply consumes its actual malloc reply once. It retains
all failure, fault, divergence, pending worlds and events; null is the adopted
allocator abort, and successful payload writes use the named OWNER suffix.
This local interpretation still needs installation in the original source run. -/
def finish (id : Nat) (h : Header) (words : PV_OWN2_ThreadInitLayout.InitWords)
    (r : Reply OWNER PV_RJ4IDB.NativeEvent Nat) : Reply OWNER PV_RJ4IDB.NativeEvent Data :=
  match r.answer with
  | .returned (.ok p) =>
    if p=0 then ⟨.fault .abort,r.world,r.events ++ [PV_STX_World.side "client-allocator-abort" []]⟩
    else if bound : p<18446744073709551616 then
      ⟨.returned (.ok (PV_THR2_OwnInitPointerCodec.encode ⟨p,bound⟩)),
        PV_OWN2_BoxConstruction.initPost r.world id h p words.handle words.data words.vtable,r.events⟩
    else ⟨.fault .abort,r.world,r.events⟩
  | .returned (.fail e) => ⟨.returned (.fail e),r.world,r.events⟩
  | .returned .div => ⟨.returned .div,r.world,r.events⟩
  | .fault f => ⟨.fault f,r.world,r.events⟩
  | .pending => ⟨.pending,r.world,r.events⟩
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
The exact24-byte resource child and adopted attempt accounting are used; there
is no receiver premise and no fixed success reply in this interpretation. -/
def reply (resources : Resources) (encode : Encode) (s : OWNER) (id : Nat)
    (h : Header) (words : PV_OWN2_ThreadInitLayout.InitWords) : Reply OWNER PV_RJ4IDB.NativeEvent Data :=
  finish id h words (PV_EVHB_AttemptAccounting.primitive resources encode id (.malloc 24) s)
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
The non-success cases are preserved before any field stores. -/
theorem other (id : Nat) (h : Header) (words : PV_OWN2_ThreadInitLayout.InitWords)
    (r : Reply OWNER PV_RJ4IDB.NativeEvent Nat) :
    (∀ e, r.answer = .returned (.fail e) → finish id h words r = ⟨.returned (.fail e),r.world,r.events⟩) ∧
    (r.answer = .returned .div → finish id h words r = ⟨.returned .div,r.world,r.events⟩) ∧
    (∀ f, r.answer = .fault f → finish id h words r = ⟨.fault f,r.world,r.events⟩) ∧
    (r.answer = .pending → finish id h words r = ⟨.pending,r.world,r.events⟩) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro e eq; simp only [finish,eq]
  · intro eq; simp only [finish,eq]
  · intro f eq; simp only [finish,eq]
  · intro eq; simp only [finish,eq]
/-- Conditional on owner acceptance of amended translator. Hypotheses: actual
nonzero represented pointer in the given FULL reply. Native return bytes and
OWNER field-store world refer to precisely that pointer and those words. -/
theorem returned (id : Nat) (h : Header) (words : PV_OWN2_ThreadInitLayout.InitWords)
    (r : Reply OWNER PV_RJ4IDB.NativeEvent Nat) (p : Pointer)
    (answer : r.answer = .returned (.ok p.val)) (nonnull : p.val ≠ 0) :
    finish id h words r =
      ⟨.returned (.ok (PV_THR2_OwnInitPointerCodec.encode p)),
        PV_OWN2_BoxConstruction.initPost r.world id h p.val words.handle words.data words.vtable,r.events⟩ := by
  simp only [finish,answer,nonnull,if_false,dif_pos p.isLt]
#print axioms other
#print axioms returned
end PV_THR2_OwnInitAllocationReply
