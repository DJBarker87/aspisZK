import NNH_AuthSeeds
set_option autoImplicit false
namespace NNH_ToLEBytes8

theorem expand (b : BitVec 64) : b.toLEBytes = [
 BitVec.setWidth 8 (b),
 BitVec.setWidth 8 (BitVec.setWidth 56 ((b) >>> 8)),
 BitVec.setWidth 8 (BitVec.setWidth 48 ((BitVec.setWidth 56 ((b) >>> 8)) >>> 8)),
 BitVec.setWidth 8 (BitVec.setWidth 40 ((BitVec.setWidth 48 ((BitVec.setWidth 56 ((b) >>> 8)) >>> 8)) >>> 8)),
 BitVec.setWidth 8 (BitVec.setWidth 32 ((BitVec.setWidth 40 ((BitVec.setWidth 48 ((BitVec.setWidth 56 ((b) >>> 8)) >>> 8)) >>> 8)) >>> 8)),
 BitVec.setWidth 8 (BitVec.setWidth 24 ((BitVec.setWidth 32 ((BitVec.setWidth 40 ((BitVec.setWidth 48 ((BitVec.setWidth 56 ((b) >>> 8)) >>> 8)) >>> 8)) >>> 8)) >>> 8)),
 BitVec.setWidth 8 (BitVec.setWidth 16 ((BitVec.setWidth 24 ((BitVec.setWidth 32 ((BitVec.setWidth 40 ((BitVec.setWidth 48 ((BitVec.setWidth 56 ((b) >>> 8)) >>> 8)) >>> 8)) >>> 8)) >>> 8)) >>> 8)),
 BitVec.setWidth 8 (BitVec.setWidth 8 ((BitVec.setWidth 16 ((BitVec.setWidth 24 ((BitVec.setWidth 32 ((BitVec.setWidth 40 ((BitVec.setWidth 48 ((BitVec.setWidth 56 ((b) >>> 8)) >>> 8)) >>> 8)) >>> 8)) >>> 8)) >>> 8)) >>> 8))] := by
 rw [BitVec.toLEBytes.eq_1]
 simp only [Nat.reduceLT,Nat.reduceSub,if_true,if_false]
 rw [BitVec.toLEBytes.eq_1]
 simp only [Nat.reduceLT,Nat.reduceSub,if_true,if_false]
 rw [BitVec.toLEBytes.eq_1]
 simp only [Nat.reduceLT,Nat.reduceSub,if_true,if_false]
 rw [BitVec.toLEBytes.eq_1]
 simp only [Nat.reduceLT,Nat.reduceSub,if_true,if_false]
 rw [BitVec.toLEBytes.eq_1]
 simp only [Nat.reduceLT,Nat.reduceSub,if_true,if_false]
 rw [BitVec.toLEBytes.eq_1]
 simp only [Nat.reduceLT,Nat.reduceSub,if_true,if_false]
 rw [BitVec.toLEBytes.eq_1]
 simp only [Nat.reduceLT,Nat.reduceSub,if_true,if_false]
 rw [BitVec.toLEBytes.eq_1]
 simp only [Nat.reduceLT,Nat.reduceSub,if_true,if_false]
 rw [BitVec.toLEBytes.eq_1]
 simp only [Nat.reduceLT,Nat.reduceSub,if_true,if_false]

#print axioms expand
end NNH_ToLEBytes8
