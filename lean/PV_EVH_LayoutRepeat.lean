import PV_EVH_CapacityWorld
set_option autoImplicit false
namespace PV_EVH_LayoutRepeat
open Aeneas.Std PV_EVH_Runtime

/-- Arithmetic specification of Rust 1.94.1 Layout padding. The bit-mask
implementation and native type size/alignment still need their association. -/
def paddedSize (size align : Nat) : Nat := size + (align - size % align) % align

def maxSize (isizeMax align : Nat) : Nat := isizeMax + 1 - align

/-- Keep machine checked_mul and Layout's tighter aligned isize check separate. -/
def repeatPacked (size align usizeMax isizeMax count : Nat) : Except Unit Layout :=
  if size * count ≤ usizeMax then
    if size * count ≤ maxSize isizeMax align then .ok ⟨size * count,align⟩
    else .error ()
  else .error ()

def layoutArray (size align usizeMax isizeMax count : Nat) : Except Unit Layout :=
  repeatPacked (paddedSize size align) align usizeMax isizeMax count

theorem already_padded (size align : Nat) (h : size % align = 0) :
    paddedSize size align = size := by
  simp only [paddedSize,h,Nat.sub_zero,Nat.mod_self,Nat.add_zero]

theorem repeat_success (size align usizeMax isizeMax count : Nat)
    (hm : size * count ≤ usizeMax)
    (hl : size * count ≤ maxSize isizeMax align) :
    repeatPacked size align usizeMax isizeMax count = .ok ⟨size * count,align⟩ := by
  simp only [repeatPacked,hm,hl,if_true]

theorem checked_mul_overflow (size align usizeMax isizeMax count : Nat)
    (hm : ¬ size * count ≤ usizeMax) :
    repeatPacked size align usizeMax isizeMax count = .error () := by
  simp only [repeatPacked,hm,if_false]

theorem layout_limit_overflow (size align usizeMax isizeMax count : Nat)
    (hm : size * count ≤ usizeMax)
    (hl : ¬ size * count ≤ maxSize isizeMax align) :
    repeatPacked size align usizeMax isizeMax count = .error () := by
  simp only [repeatPacked,hm,hl,if_true,if_false]

/-- Refines the earlier CapacityWorld helper on a native metadata domain.
No concrete element size, power-of-two alignment or target width is assumed. -/
theorem capacity_layout_agreement (size align usizeMax isizeMax : Nat) (count : Usize)
    (hp : size % align = 0) (hbound : maxSize isizeMax align ≤ usizeMax) :
    layoutArray size align usizeMax isizeMax count.val =
      PV_EVH_CapacityWorld.layoutFor size align (maxSize isizeMax align) count := by
  rw [layoutArray,already_padded size align hp]
  unfold repeatPacked PV_EVH_CapacityWorld.layoutFor
  by_cases h : size * count.val ≤ maxSize isizeMax align
  · have hm := Nat.le_trans h hbound
    simp only [h,hm,if_true]
  · by_cases hm : size * count.val ≤ usizeMax
    · simp only [h,hm,if_true,if_false]
    · simp only [h,hm,if_false]

#print axioms already_padded
#print axioms repeat_success
#print axioms checked_mul_overflow
#print axioms layout_limit_overflow
#print axioms capacity_layout_agreement
end PV_EVH_LayoutRepeat
