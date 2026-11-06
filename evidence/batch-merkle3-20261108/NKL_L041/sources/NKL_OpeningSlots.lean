import NKL_ReadWindows
set_option autoImplicit false
noncomputable section
namespace NKL_OpeningSlots
open Aeneas Aeneas.Std Result AspisR1
open NKL_CanonicalWindows

def P (q : Slice U8) (s : Nat) : Prop :=
 (∀ l,l<26→W q (30*s+l)) ∧ (∀ j,j<4→W q (30*s+26+j)) ∧
 (∀ j,j<4→W q (120+8*s+j)) ∧ (∀ j,j<4→W q (120+8*s+4+j))

theorem scalars (q : Slice U8) (width:q.val.length=832) (s : Usize) (slot:s.val<4) :
 NKB_CanonicalPair.allFrom (NKB_CanonicalScalarLoop.pass NKB_CanonicalScalarBridge.scalar q s) 0 26=true ↔
 ∀ l,l<26→W q (30*s.val+l) := by
 rw [NKL_CanonicalWindows.allFrom]
 simp only [Nat.zero_add,Nat.zero_le,true_implies]
 apply forall_congr'
 intro l
 apply imp_congr_right
 intro lane
 have iv: (NKB_CanonicalScalarLoop.index l).val=l := NKL_CanonicalWindows.index l (by omega)
 have h:=NKL_ReadWindows.scalar q width s (NKB_CanonicalScalarLoop.index l) slot (by rw [iv];exact lane)
 simpa only [iv] using h

theorem slot (q : Slice U8) (width:q.val.length=832) (s : Usize) (bound:s.val<4) :
 NKB_CanonicalOpening.slot NKB_CanonicalScalarBridge.scalar NKL_CanonicalKCarrier.selected q s=true ↔ P q s.val := by
 unfold NKB_CanonicalOpening.slot NKB_CanonicalTail.accepted P
 simp only [Bool.and_eq_true,scalars q width s bound,NKL_ReadWindows.c1 q width s bound,
  NKL_ReadWindows.c2 q width s 0#usize bound (by decide),
  NKL_ReadWindows.c2 q width s 1#usize bound (by decide),
  show (0#usize).val=0 from rfl,show (1#usize).val=1 from rfl,
  Nat.mul_zero,Nat.mul_one,Nat.add_zero,and_assoc]

theorem all_slots (q : Slice U8) (width:q.val.length=832) :
 NKB_CanonicalPair.allFrom
  (NKB_CanonicalSlotLoop.pass NKB_CanonicalScalarBridge.scalar NKL_CanonicalKCarrier.selected q) 0 4=true ↔
 ∀ s,s<4→P q s := by
 rw [NKL_CanonicalWindows.allFrom]
 simp only [Nat.zero_add,Nat.zero_le,true_implies]
 apply forall_congr'
 intro s
 apply imp_congr_right
 intro bound
 have iv:(NKB_CanonicalScalarLoop.index s).val=s := NKL_CanonicalWindows.index s (by omega)
 have active:(NKB_CanonicalScalarLoop.index s).val<4 := by rw [iv];exact bound
 have actual:=NKB_CanonicalSlotLoop.actual NKB_CanonicalScalarBridge.scalar NKL_CanonicalKCarrier.selected q
  (NKB_CanonicalScalarLoop.index s) active
 rw [iv] at actual
 rw [actual,slot q width _ active,iv]

theorem cover (q : Slice U8) : (∀ s,s<4→P q s) ↔ ∀ j,j<152→W q j := by
 constructor
 · intro native j bound
   by_cases first:j<120
   · have row:=native (j/30) (by omega)
     by_cases scalar:j%30<26
     · have h:=row.1 (j%30) scalar
       have address:30*(j/30)+j%30=j := by omega
       simpa only [address] using h
     · have h:=row.2.1 (j%30-26) (by omega)
       have address:30*(j/30)+26+(j%30-26)=j := by omega
       simpa only [address] using h
   · have row:=native ((j-120)/8) (by omega)
     by_cases low:(j-120)%8<4
     · have h:=row.2.2.1 ((j-120)%8) low
       have address:120+8*((j-120)/8)+(j-120)%8=j := by omega
       simpa only [address] using h
     · have h:=row.2.2.2 ((j-120)%8-4) (by omega)
       have address:120+8*((j-120)/8)+4+((j-120)%8-4)=j := by omega
       simpa only [address] using h
 · intro words s bound
   exact ⟨fun l lane=>words _ (by omega),fun j lane=>words _ (by omega),
    fun j lane=>words _ (by omega),fun j lane=>words _ (by omega)⟩

#print axioms scalars
#print axioms slot
#print axioms all_slots
#print axioms cover
end NKL_OpeningSlots
end
