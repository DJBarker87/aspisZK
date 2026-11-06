import NKL_OpeningSlots
import NKL_ChildCanonical
set_option autoImplicit false
noncomputable section
namespace NKL_OpeningCanonical
open Aeneas Aeneas.Std Result AspisR1
open OraclePortCompactDraft MultiproofConeCanonical NKL_CanonicalWindows
attribute [local instance] Classical.propDecidable

def native (q : Slice U8) : Bool :=
 NKB_CanonicalPair.allFrom
  (NKB_CanonicalSlotLoop.pass NKB_CanonicalScalarBridge.scalar NKL_CanonicalKCarrier.selected q) 0 4 &&
 NKL_CanonicalChildren.echeckGood (NKB_CanonicalOpening.trailing q)

theorem source (q : Slice U8) (width:q.val.length=832) :
 native q=true ↔ openingCanonical (bytesOf q.val) := by
 have front : canonical ((bytesOf q.val).take 608) ↔ ∀ j,j<152→W q j := by
  simpa only [slice,List.drop_zero,Nat.mul_zero,Nat.zero_add] using
   (NKL_CanonicalWindows.canonical_window q width 0 152 (by decide))
 have len:=NKB_CanonicalDomains.trailing q width
 have back:=NKL_ChildCanonical.echeck (NKB_CanonicalOpening.trailing q) (by omega)
 have view : bytesOf (NKB_CanonicalOpening.trailing q).val=slice (bytesOf q.val) 672 128 := by
  simp only [NKB_CanonicalOpening.trailing,MultiproofConeSlices.bytes_sub]
  rfl
 rw [view] at back
 unfold native openingCanonical
 rw [Bool.and_eq_true,NKL_OpeningSlots.all_slots q width,NKL_OpeningSlots.cover,←front,back]

theorem decide (q : Slice U8) (width:q.val.length=832) :
 native q=_root_.decide (openingCanonical (bytesOf q.val)) := by
 have meaning:=source q width
 cases h:native q <;> simp_all

#print axioms source
#print axioms decide
end NKL_OpeningCanonical
end
