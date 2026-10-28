import NCV_FieldViews
import NCV_CallerDomains
set_option autoImplicit false
namespace NDB_WindowGeometry
open Aeneas Aeneas.Std Result AspisR1
/-- Absolute reads are the same reads in the Kani one-window harness. -/
theorem row (b : Slice U8) (base width count k : Nat) (index : k<count) :
    JHg_FieldRead.segment (JHg_FieldRead.segment b base (width*count)) (width*k) width=
      JHg_FieldRead.segment b (base+width*k) width := by
  apply NCV_FieldViews.nested
  have h := Nat.mul_le_mul_left width (show k+1 ≤ count by omega)
  simpa only [Nat.mul_add,Nat.mul_one] using h

theorem master (b : Slice U8) (k : Nat) (index : k<8) (length : b.val.length=384) :
    (JHg_FieldRead.segment b (320+8*k) 8).val.length=8 ∧
      JHg_FieldRead.segment (JHg_FieldRead.segment b 320 64) (8*k) 8=
        JHg_FieldRead.segment b (320+8*k) 8 := by
  refine ⟨JHg_FieldRead.length b _ _ (by omega),?_⟩
  exact row b 320 8 8 k index

theorem checkpoint (b : Slice U8) (k : Nat) (index : k<8) (length : b.val.length=192) :
    (JHg_FieldRead.segment b (112+8*k) 8).val.length=8 ∧
      JHg_FieldRead.segment (JHg_FieldRead.segment b 112 64) (8*k) 8=
        JHg_FieldRead.segment b (112+8*k) 8 := by
  refine ⟨JHg_FieldRead.length b _ _ (by omega),?_⟩
  exact row b 112 8 8 k index

theorem lane (b : Slice U8) (level : Nat) (index : level<20) (length : b.val.length=768) :
    (JHg_FieldRead.segment b (128+32*level) 32).val.length=32 ∧
      JHg_FieldRead.segment (JHg_FieldRead.segment b 80 688) (48+32*level) 32=
        JHg_FieldRead.segment b (128+32*level) 32 := by
  refine ⟨JHg_FieldRead.length b _ _ (by omega),?_⟩
  have eq : 80+(48+32*level)=128+32*level := by omega
  simpa only [eq] using NCV_FieldViews.nested b 80 688 (48+32*level) 32 (by omega)
#print axioms row
#print axioms master
#print axioms checkpoint
#print axioms lane
end NDB_WindowGeometry
