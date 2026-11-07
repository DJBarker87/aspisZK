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
 simp only [show ((64 : Nat)>0) by decide,if_true,if_false,Nat.reduceSub]
 rw [BitVec.toLEBytes.eq_1]
 simp only [show ((56 : Nat)>0) by decide,if_true,if_false,Nat.reduceSub]
 rw [BitVec.toLEBytes.eq_1]
 simp only [show ((48 : Nat)>0) by decide,if_true,if_false,Nat.reduceSub]
 rw [BitVec.toLEBytes.eq_1]
 simp only [show ((40 : Nat)>0) by decide,if_true,if_false,Nat.reduceSub]
 rw [BitVec.toLEBytes.eq_1]
 simp only [show ((32 : Nat)>0) by decide,if_true,if_false,Nat.reduceSub]
 rw [BitVec.toLEBytes.eq_1]
 simp only [show ((24 : Nat)>0) by decide,if_true,if_false,Nat.reduceSub]
 rw [BitVec.toLEBytes.eq_1]
 simp only [show ((16 : Nat)>0) by decide,if_true,if_false,Nat.reduceSub]
 rw [BitVec.toLEBytes.eq_1]
 simp only [show ((8 : Nat)>0) by decide,if_true,if_false,Nat.reduceSub]
 rw [BitVec.toLEBytes.eq_1]
 simp only [show ¬((0 : Nat)>0) by decide,if_true,if_false,Nat.reduceSub]

#print axioms expand
end NNH_ToLEBytes8
