import NGV_SemanticFrames
import NGV_RowValues
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_SemanticValues
open NGV_SemanticTrace NGV_RowPayload
/-- Every payload byte is fixed by the original compact source, independently
of the arbitrary output prestate. -/
def payloadByte (input : Slice U8) (r j : Nat) : U8 :=
 if r<14 then input.val[NGD_SemanticSchedule.src r+5+j]?.getD 0#u8
 else NFU_Retarget.LPl_A.Expand.byte (source input r).val j
theorem rows (input before final : Slice U8) (r : Nat) (run : Run input r before final) :
 (inputSize : input.val.length=7015) → (outputSize : before.val.length=13831) →
 ∀ wanted,r≤wanted→wanted<27→
   (∀ j,j<5→final.val[NGD_SemanticSchedule.dst wanted+j]?=input.val[NGD_SemanticSchedule.src wanted+j]?) ∧
   (∀ j,j<NFU_PacketDomains.payloadSize wanted→
     final.val[NGD_SemanticSchedule.dst wanted+5+j]?.getD 0#u8=payloadByte input wanted j) := by
 induction run with
 | done before => intro _ _ wanted low high;omega
 | next r before live packet final rest ih =>
   intro inputSize outputSize wanted low high
   by_cases same:wanted=r
   · subst wanted
     have advance:NGD_SemanticSchedule.dst (r+1)=NGD_SemanticSchedule.dst r+5+NFU_PacketDomains.payloadSize r :=
       (NGD_SemanticSchedule.advance r live).2
     refine ⟨?_,?_⟩
     · intro j within
       have frame:=NGV_SemanticFrames.preserved_prefix input (after packet) final (r+1) rest inputSize
         (NGD_SemanticSchedule.dst r+j) (by rw [advance];omega)
       exact frame.trans (NGV_RowValues.header input before r j live within inputSize outputSize packet)
     · intro j within
       have frame:=NGV_SemanticFrames.preserved_prefix input (after packet) final (r+1) rest inputSize
         (NGD_SemanticSchedule.dst r+5+j) (by rw [advance];omega)
       rw [frame,NGV_RowValues.payload input before r j live within outputSize packet]
       by_cases compacted:14≤r
       · simp only [payloadByte,if_neg (by omega : ¬r<14)]
         exact packet.bytes compacted j within
       · have ordinary:r<14 := by omega
         rw [packet.low ordinary]
         have stored:NGD_SemanticSchedule.stored r=NFU_PacketDomains.payloadSize r := by
           simp only [NGD_SemanticSchedule.stored,if_neg compacted]
         simp [payloadByte,ordinary,source,NGV_ByteWindow.select,show j<NGD_SemanticSchedule.stored r by omega]
   · exact ih inputSize ((NGV_RowPayload.length packet).trans outputSize) wanted (by omega) high
#print axioms rows
end NGV_SemanticValues
