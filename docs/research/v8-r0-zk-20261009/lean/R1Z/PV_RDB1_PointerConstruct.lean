import R1Z.PV_RDB1_Pointer
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_PointerConstruct
open PV_RDB1_Pointer

def fromRef {T P : Type} (reference : Ptr T P) : NonNull T P := ⟨reference⟩
def fromMut {T P : Type} (reference : Ptr T P) : NonNull T P := ⟨reference⟩
def transparentWrap {T P : Type} (p : Ptr T P) : NonNull T P := ⟨p⟩

theorem from_ref_complete {T P W : Type} (p : Ptr T P) (w : W) :
    (ok (fromRef p,w) : Result (NonNull T P × W)) = ok (transparentWrap p,w) := rfl

theorem from_mut_complete {T P W : Type} (p : Ptr T P) (w : W) :
    (ok (fromMut p,w) : Result (NonNull T P × W)) = ok (transparentWrap p,w) := rfl

def withoutProvenance {T P : Type} (addr : Nat) : NonNull T (Option P) :=
  ⟨⟨none,addr⟩⟩

theorem without_provenance_complete {T P W : Type} (addr : Nat) (w : W) :
    (ok (withoutProvenance (T:=T) (P:=P) addr,w) : Result (NonNull T (Option P) × W)) =
      ok (transparentWrap (⟨none,addr⟩ : Ptr T (Option P)),w) := rfl

def checked {T P : Type} (p : Ptr T P) : Option (NonNull T P) :=
  if p.address=0 then none else some ⟨p⟩

theorem checked_complete {T P : Type} (p : Ptr T P) :
    checked p = (if p.address=0 then none else some (transparentWrap p)) := rfl

theorem checked_success {T P : Type} (p : Ptr T P) (nonnull : p.address ≠ 0) :
    checked p = some ⟨p⟩ := by simp only [checked,nonnull,ite_false]

structure Slice (T P : Type) where
  data : NonNull T P
  len : Nat

def deployedSlice {T P : Type} (p : NonNull T P) (len : Nat) : Slice T P := ⟨p,len⟩
def historicalSlice {T P : Type} (p : NonNull T P) (len : Nat) : Slice T P := ⟨p,len⟩

theorem slice_complete {T P W : Type} (p : NonNull T P) (len : Nat) (w : W) :
    (ok (deployedSlice p len,w) : Result (Slice T P × W)) =
      ok (historicalSlice p len,w) := rfl

def allocated {P W : Type} (size : Nat) (p : Ptr U8 P) (w : W) :
    Except Unit (Slice U8 P) × W :=
  (match checked p with
    | none => .error ()
    | some q => .ok (deployedSlice q size),w)

/-- Full null/error/success mapping after an arbitrary allocator step. Its
private state has already advanced even when the pointer is null. -/
theorem allocated_complete {P W : Type} (size : Nat) (p : Ptr U8 P) (w : W) :
    allocated size p w =
      ((if p.address=0 then .error () else .ok (historicalSlice ⟨p⟩ size)),w) := by
  by_cases h : p.address=0 <;> simp only [allocated,checked,h,ite_true,ite_false,
    deployedSlice,historicalSlice]

#print axioms from_ref_complete
#print axioms from_mut_complete
#print axioms without_provenance_complete
#print axioms checked_complete
#print axioms checked_success
#print axioms slice_complete
#print axioms allocated_complete
end R1Z.PV_RDB1_PointerConstruct
