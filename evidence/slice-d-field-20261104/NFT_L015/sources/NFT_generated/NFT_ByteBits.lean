import NFQ_STAGE2_IMPORT
import Std.Tactic.BVDecide
set_option autoImplicit false
namespace NFT_ByteBits

theorem lane2 (x : BitVec 32) :
    BitVec.setWidth 8 (x >>> 16)=BitVec.setWidth 8 (BitVec.setWidth 24 (x >>> 8) >>> 8) := by
  bv_decide

theorem lane3 (x : BitVec 32) :
    BitVec.setWidth 8 (x >>> 24)=
      BitVec.setWidth 8 (BitVec.setWidth 16 (BitVec.setWidth 24 (x >>> 8) >>> 8) >>> 8) := by
  bv_decide

#print axioms lane2
#print axioms lane3
end NFT_ByteBits
