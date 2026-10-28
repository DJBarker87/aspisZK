import NDO_JGd_MaskModel
import AspisV8R17.QM31WordTower
import NDO_JFr_WordArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_ExactWords
abbrev W := (Nat × Nat) × (Nat × Nat)
abbrev Q := AspisV8R15.ExactTowerBase.QM31Exact
def value (w : W) : Q := AspisV8R17.QM31WordTower.decodeQ w

theorem add (x y z : W) (h : AspisV8R17.GeneratedQM31Linear.qmAddWords x y = z) :
    value x + value y = value z :=
  (AspisV8R17.QM31WordTower.decode_add x y).symm.trans (congrArg value h)
theorem mul (x y z : W) (h : AspisV8R17.GeneratedQM31Products.qmMulWords x y = z) :
    value x * value y = value z :=
  (AspisV8R17.QM31WordTower.decode_mul x y).symm.trans (congrArg value h)
theorem natCast (n : Nat) : value ((n,0),(0,0)) = (n : Q) := by rfl
theorem decode (x : FIp_SemanticArithmetic.PQ) :
    ExtractedMaskQM31Exact.decode x = value ((x.c0.a.val,x.c0.b.val),(x.c1.a.val,x.c1.b.val)) := rfl
#print axioms add
#print axioms mul
#print axioms natCast
#print axioms decode
end AspisR1.JGd_ExactWords
end
