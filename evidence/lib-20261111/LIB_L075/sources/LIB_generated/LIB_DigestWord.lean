import LIB_Carriers
import NFY_Part005
import NND_Carrier
import RSL_TX2_217
set_option autoImplicit false
namespace LIB_DigestWord
open Aeneas Aeneas.Std
#print BitVec.fromLEBytes
/-- Four symbolic bytes; the primitive little-endian carrier association. -/
theorem four (a b c d : U8) :
 NND_Carrier.word (core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])) =
 RSL.le32 (NND_Carrier.byte a) (NND_Carrier.byte b)
   (NND_Carrier.byte c) (NND_Carrier.byte d) := by
 cases a with
 | mk a =>
  cases b with
  | mk b =>
   cases c with
   | mk c =>
    cases d with
    | mk d =>
     apply UInt32.toBitVec_inj.mp
     change BitVec.fromLEBytes [a,b,c,d] =
       a.setWidth 32 ||| (b.setWidth 32 <<< 8) |||
         (c.setWidth 32 <<< 16) ||| (d.setWidth 32 <<< 24)
     apply BitVec.eq_of_getLsbD_eq
     intro i hi
     have h := BitVec.fromLEBytes_getElem! [a,b,c,d] i
     rw [BitVec.getElem!_eq_getElem _ _ hi,
       BitVec.getElem_eq_testBit_toNat,BitVec.testBit_toNat] at h
     rw [h]
     change i < 32 at hi
     by_cases h0 : i < 8
     · have hd : i / 8 = 0 := by omega
       have hm : i % 8 = i := by omega
       simp (disch := omega) [hd,hm,BitVec.getLsbD_or,BitVec.getLsbD_setWidth,
         BitVec.getLsbD_shiftLeft,BitVec.testBit_toNat,hi,h0]
     · by_cases h1 : i < 16
       · have hd : i / 8 = 1 := by omega
         have hm : i % 8 = i - 8 := by omega
         simp (disch := omega) [hd,hm,BitVec.getLsbD_or,BitVec.getLsbD_setWidth,
           BitVec.getLsbD_shiftLeft,BitVec.testBit_toNat,BitVec.getLsbD_of_ge,hi,h0,h1]
       · by_cases h2 : i < 24
         · have hd : i / 8 = 2 := by omega
           have hm : i % 8 = i - 16 := by omega
           simp (disch := omega) [hd,hm,BitVec.getLsbD_or,BitVec.getLsbD_setWidth,
             BitVec.getLsbD_shiftLeft,BitVec.testBit_toNat,BitVec.getLsbD_of_ge,hi,h0,h1,h2]
         · have hd : i / 8 = 3 := by omega
           have hm : i % 8 = i - 24 := by omega
           simp (disch := omega) [hd,hm,BitVec.getLsbD_or,BitVec.getLsbD_setWidth,
             BitVec.getLsbD_shiftLeft,BitVec.testBit_toNat,BitVec.getLsbD_of_ge,hi,h0,h1,h2]
#print axioms four
end LIB_DigestWord
