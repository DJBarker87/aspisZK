import NMX_BvByte
set_option autoImplicit false
namespace NMX_LEFirst
/-- One symbolic byte constructor. The recursive tail remains folded. -/
theorem step {w : Nat} (x : BitVec w) (positive : 0 < w) :
 x.toLEBytes = x.setWidth 8 :: ((x >>> 8).setWidth (w-8)).toLEBytes := by
 rw [BitVec.toLEBytes.eq_1]
 simp only [positive,↓reduceIte]
#print axioms step
end NMX_LEFirst
