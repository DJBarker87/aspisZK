import NGV_SemanticInitial
import NGV_SemanticValues
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_SemanticPacket
open AspisS1NativeCompact NGV_SemanticTrace NGV_SemanticInitial
/-- Constructed original native trace and complete adopted result, with the
initial 32 bytes, every row header and every expanded payload value on the SAME
arbitrary output. Only the root's original dimensions are premises. -/
theorem result (input out : Slice U8) (inputSize : input.val.length=7015)
 (outputSize : out.val.length=13831) :
 ∃ final : Slice U8,
 compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues input out=ok (.Ok (),final) ∧
 Run input 0 (initial input out) final ∧
 final.val.length=13831 ∧
 (∀ j,j<32→final.val[j]?=input.val[j]?) ∧
 (∀ row,row<27→
   (∀ j,j<5→final.val[NGD_SemanticSchedule.dst row+j]?=input.val[NGD_SemanticSchedule.src row+j]?) ∧
   (∀ j,j<NFU_PacketDomains.payloadSize row→
     final.val[NGD_SemanticSchedule.dst row+5+j]?.getD 0#u8=NGV_SemanticValues.payloadByte input row j)) := by
 have initialSize : (initial input out).val.length=13831 := by
   unfold initial
   rw [NGV_ByteWindow.write_length,outputSize]
 obtain ⟨final,run⟩:=NGV_SemanticTrace.construct input (initial input out) 0 (by omega) inputSize initialSize
 have model:=NGV_SemanticTrace.result input 0 (initial input out) final run (by omega) inputSize initialSize 0#u8 rfl
 have sourceZero : NGV_Cursors.src 0 (by omega)=32#usize := UScalar.eq_of_val_eq rfl
 have outputZero : NGV_Cursors.dst 0 (by omega)=32#usize := UScalar.eq_of_val_eq rfl
 rw [sourceZero,outputZero] at model
 have call : compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues input out=ok (.Ok (),final) := by
   rw [emitted _ input out inputSize outputSize,copied input out inputSize outputSize,bind_tc_ok]
   exact model
 refine ⟨final,call,run,(NGV_SemanticFrames.length input (initial input out) final 0 run).trans initialSize,?_,?_⟩
 · intro j within
   have frame:=NGV_SemanticFrames.preserved_prefix input (initial input out) final 0 run inputSize j (by
     change j<32;exact within)
   rw [frame]
   simp only [initial,NGV_ByteWindow.write,Slice.setSlice!_val]
   rw [List.setSlice!_getElem?_middle _ _ 0 j (by
     rw [NGV_ByteWindow.select_length input 0 32 (by omega)]
     constructor
     · omega
     · constructor <;> omega)]
   simp [NGV_ByteWindow.select,within]
 · intro row live
   exact NGV_SemanticValues.rows input (initial input out) final 0 run inputSize initialSize row (by omega) live
/-- Symbolic interval coverage, without enumerating the 13,831-byte output. -/
theorem intervals (f : Nat→Nat) (n j : Nat) (lower : f 0≤j) (upper : j<f n) :
 ∃ r,r<n ∧ f r≤j ∧ j<f (r+1) := by
 induction n with
 | zero => omega
 | succ n ih =>
   by_cases previous:j<f n
   · obtain ⟨r,live,start,finish⟩:=ih previous
     exact ⟨r,by omega,start,finish⟩
   · exact ⟨n,by omega,by omega,upper⟩
/-- The exported byte observations cover every position of the SAME output. -/
theorem coverage (j : Nat) (inside : j<13831) :
 j<32 ∨ ∃ row,row<27 ∧ NGD_SemanticSchedule.dst row≤j ∧
   j<NGD_SemanticSchedule.dst row+5+NFU_PacketDomains.payloadSize row := by
 by_cases first:j<32
 · exact Or.inl first
 · right
   obtain ⟨row,live,start,finish⟩:=intervals NGD_SemanticSchedule.dst 27 j (by change 32≤j;omega) (by change j<13831;exact inside)
   refine ⟨row,live,start,?_⟩
   rw [←(NGD_SemanticSchedule.advance row live).2]
   exact finish
#print axioms result
#print axioms intervals
#print axioms coverage
end NGV_SemanticPacket
