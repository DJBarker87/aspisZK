import NGV_SemanticArithmetic
import NGV_SemanticDomains
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_Cursors
def src (r : Nat) (bound : r≤27) : Usize := UScalar.ofNat (NGD_SemanticSchedule.src r) (by
 have h:=NGD_SemanticSchedule.src_mono r 27 bound (by omega)
 have finish:=NGD_SemanticSchedule.finish
 scalar_tac)
def dst (r : Nat) (bound : r≤27) : Usize := UScalar.ofNat (NGD_SemanticSchedule.dst r) (by
 have h:=NGD_SemanticSchedule.dst_mono r 27 bound (by omega)
 have finish:=NGD_SemanticSchedule.finish
 scalar_tac)
def srcHead (r : Nat) (live : r<27) : Usize := UScalar.ofNat (NGD_SemanticSchedule.src r+5) (by
 have h:=(NGD_SemanticSchedule.windows r live).1;scalar_tac)
def dstHead (r : Nat) (live : r<27) : Usize := UScalar.ofNat (NGD_SemanticSchedule.dst r+5) (by
 have h:=(NGD_SemanticSchedule.windows r live).2.1;scalar_tac)
theorem source_add (r : Nat) (live : r<27) : src r (by omega)+5#usize=ok (srcHead r live) := by
 apply NGV_SemanticArithmetic.add;rfl
theorem output_add (r : Nat) (live : r<27) : dst r (by omega)+5#usize=ok (dstHead r live) := by
 apply NGV_SemanticArithmetic.add;rfl
theorem advance (r : Nat) (live : r<27) (size : Usize)
 (sizeValue : size.val=NFU_PacketDomains.payloadSize r) :
 (dst (r+1) (by omega)).val=(dstHead r live).val+size.val ∧
 (r<14 → (src (r+1) (by omega)).val=(srcHead r live).val+size.val) ∧
 (14≤r → (src (r+1) (by omega)).val=(srcHead r live).val+size.val/2) := by
 have step:=NGD_SemanticSchedule.advance r live
 change NGD_SemanticSchedule.dst (r+1)=NGD_SemanticSchedule.dst r+5+size.val ∧
   (r<14 → NGD_SemanticSchedule.src (r+1)=NGD_SemanticSchedule.src r+5+size.val) ∧
   (14≤r → NGD_SemanticSchedule.src (r+1)=NGD_SemanticSchedule.src r+5+size.val/2)
 refine ⟨by rw [sizeValue];exact step.2,?_,?_⟩
 · intro low
   have stored : NGD_SemanticSchedule.stored r=NFU_PacketDomains.payloadSize r := by
     simp only [NGD_SemanticSchedule.stored,if_neg (by omega : ¬14≤r)]
   rw [sizeValue,←stored];exact step.1
 · intro high
   rw [sizeValue]
   simpa only [NGD_SemanticSchedule.stored,if_pos high] using step.1
#print axioms source_add
#print axioms output_add
#print axioms advance
end NGV_Cursors
