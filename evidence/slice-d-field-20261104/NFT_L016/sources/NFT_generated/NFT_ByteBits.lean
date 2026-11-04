import NFQ_STAGE2_IMPORT
set_option autoImplicit false
namespace NFT_ByteBits

theorem lane2 (x : BitVec 32) :
    BitVec.setWidth 8 (x >>> 16)=BitVec.setWidth 8 (BitVec.setWidth 24 (x >>> 8) >>> 8) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_setWidth,BitVec.getLsbD_ushiftRight,BitVec.getLsbD_setWidth]
  simp [show 8+i<24 by omega,show 8+i<16 by omega,
    show 8+(8+i)<24 by omega,Nat.add_assoc]

theorem lane3 (x : BitVec 32) :
    BitVec.setWidth 8 (x >>> 24)=
      BitVec.setWidth 8 (BitVec.setWidth 16 (BitVec.setWidth 24 (x >>> 8) >>> 8) >>> 8) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_setWidth,BitVec.getLsbD_ushiftRight,BitVec.getLsbD_setWidth]
  simp [show 8+i<24 by omega,show 8+i<16 by omega,
    show 8+(8+i)<24 by omega,Nat.add_assoc]

#print axioms lane2
#print axioms lane3
end NFT_ByteBits
