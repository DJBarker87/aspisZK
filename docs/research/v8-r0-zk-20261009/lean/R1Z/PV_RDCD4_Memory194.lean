import Aeneas
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDCD4_Memory194
set_option autoImplicit false

/-- Typed source-memory coordinates. origin is a logical allocation token,
not an observed machine address. Layout and intrinsic execution remain V370. -/
structure Pointer (E : Type) where
  origin : Nat
  data : List E
  offset : Nat
  deriving Repr
structure Span (E : Type) where
  pointer : Pointer E
  len : Nat
  deriving Repr

def valid {E : Type} (p : Pointer E) (len : Nat) : Prop :=
  p.offset + len ≤ p.data.length

def advance {E : Type} (p : Pointer E) (n : Nat) : Pointer E :=
  {p with offset := p.offset+n}

def aggregate {E : Type} (p : Pointer E) (len : Nat) : Span E := ⟨p,len⟩
def metadataFromRawParts {E : Type} (p : Pointer E) (len : Nat) : Span E :=
  aggregate p len
def ptrSliceFromRawParts {E : Type} (p : Pointer E) (len : Nat) : Span E :=
  metadataFromRawParts p len
def sliceRawFromRawParts {E : Type} (p : Pointer E) (len : Nat) : Span E :=
  ptrSliceFromRawParts p len

def values {E : Type} (s : Span E) : List E :=
  (s.pointer.data.drop s.pointer.offset).take s.len

/-- The undefined model arm represents an invalid raw read, not a new safe
Rust failure. Every consumed read is proved within initialized storage. -/
def primitiveRead {E : Type} (p : Pointer E) : Result E :=
  match p.data[p.offset]? with
  | some v => ok v
  | none => fail .undef

def ptrRead {E : Type} (p : Pointer E) : Result E := primitiveRead p
def constPtrRead {E : Type} (p : Pointer E) : Result E := ptrRead p

theorem read_forward {E : Type} (p : Pointer E) :
    constPtrRead p=ptrRead p := rfl

theorem read_at {E : Type} (p : Pointer E) (h : p.offset < p.data.length) :
    constPtrRead p=ok p.data[p.offset] := by
  simp only [constPtrRead,ptrRead,primitiveRead,List.getElem?_eq_getElem h]

theorem read_frame {E : Type} (p : Pointer E) (h : p.offset < p.data.length) :
    (do let v ← constPtrRead p; ok (v,p))=ok (p.data[p.offset],p) := by
  rw [read_at p h,bind_tc_ok]

theorem raw_parts_forward {E : Type} (p : Pointer E) (len : Nat) :
    sliceRawFromRawParts p len=ptrSliceFromRawParts p len := rfl

theorem metadata_forward {E : Type} (p : Pointer E) (len : Nat) :
    ptrSliceFromRawParts p len=metadataFromRawParts p len := rfl

theorem raw_parts_fields {E : Type} (p : Pointer E) (len : Nat) :
    (sliceRawFromRawParts p len).pointer=p ∧
    (sliceRawFromRawParts p len).len=len := ⟨rfl,rfl⟩

theorem length {E : Type} (p : Pointer E) (len : Nat) (h : valid p len) :
    (values (sliceRawFromRawParts p len)).length=len := by
  simp only [values,sliceRawFromRawParts,ptrSliceFromRawParts,
    metadataFromRawParts,aggregate,List.length_take,List.length_drop]
  exact Nat.min_eq_left (by unfold valid at h; omega)

#print axioms read_forward
#print axioms read_at
#print axioms read_frame
#print axioms raw_parts_forward
#print axioms metadata_forward
#print axioms raw_parts_fields
#print axioms length
end R1Z.PV_RDCD4_Memory194
