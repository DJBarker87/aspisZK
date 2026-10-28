import R1Z.PV_RDB1_PointerConstruct
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_ByteSlice
open PV_RDB1_Pointer

structure Ref (P : Type) where
  data : Ptr U8 P
  length : Nat
structure Iter (P : Type) where
  start : Ptr U8 P
  finish : Ptr U8 P

def fresh {P : Type} (s : Ref P) : Iter P :=
  ⟨s.data,offset s.data s.length 1⟩

def view {P : Type} (i : Iter P) : Ref P :=
  ⟨i.start,i.finish.address-i.start.address⟩

/-- Iter::new for bytes followed immediately by Iter::as_slice returns the
same data pointer/provenance and exact metadata length. This is the actual
SpecExtend<&u8,Iter<u8>> route; no iterator element is consumed or repeated. -/
theorem fresh_view {P : Type} (s : Ref P) : view (fresh s)=s := by
  cases s with
  | mk data length =>
    simp only [view,fresh,offset,Nat.mul_one,Nat.add_sub_cancel_left]

/-- Dropping slice metadata during a cast to a SIZED byte pointer does not
drop the metadata length previously read by Iter::new. -/
def castData {P : Type} (s : Ref P) : NonNull U8 P := ⟨s.data⟩

theorem fat_cast_complete {P W : Type} (s : Ref P) (w : W) :
    (ok (castData s,s.length,w) : Result (NonNull U8 P × Nat × W)) =
      ok (⟨s.data⟩,s.length,w) := rfl

theorem distance (base count width : Nat) (positive : 0<width) :
    (base+count*width-base)/width=count := by
  rw [Nat.add_sub_cancel_left,Nat.mul_div_cancel _ positive]

#print axioms fresh_view
#print axioms fat_cast_complete
#print axioms distance
end R1Z.PV_RDB1_ByteSlice
