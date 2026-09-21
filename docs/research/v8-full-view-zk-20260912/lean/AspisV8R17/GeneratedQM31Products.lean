import AspisV8R17.GeneratedQM31Scalar
import AspisV8R17.GeneratedMulByR
import AspisV8R17.GeneratedCM31SquareNormalized
import AspisV8R17.QM31WordFormulas

namespace V7Tag73CurrentHelpersOpaque
open Aeneas Aeneas.Std Result
-- GENERATED FunsChunk04.lean
@[rust_fun "aspis_core::field::{aspis_core::field::QM31}::square"]
def aspis_core.field.QM31.square
  (self : aspis_core.field.QM31) : Result aspis_core.field.QM31 := do
  let c0_square ← aspis_core.field.CM31.square self.c0
  let c1_square ← aspis_core.field.CM31.square self.c1
  let c ← aspis_core.field.mul_by_r c1_square
  let c1 ← aspis_core.field.CM31.add c0_square c
  let c2 ← aspis_core.field.CM31.mul self.c0 self.c1
  let c3 ← aspis_core.field.CM31.double c2
  ok { c0 := c1, c1 := c3 }
-- END GENERATED

-- GENERATED FunsChunk04.lean
@[rust_fun "aspis_core::field::{aspis_core::field::QM31}::mul"]
def aspis_core.field.QM31.mul
  (self : aspis_core.field.QM31) (rhs : aspis_core.field.QM31) :
  Result aspis_core.field.QM31
  := do
  let m0 ← aspis_core.field.CM31.mul self.c0 rhs.c0
  let m1 ← aspis_core.field.CM31.mul self.c1 rhs.c1
  let c ← aspis_core.field.CM31.add self.c0 self.c1
  let c1 ← aspis_core.field.CM31.add rhs.c0 rhs.c1
  let m2 ← aspis_core.field.CM31.mul c c1
  let c2 ← aspis_core.field.mul_by_r m1
  let c3 ← aspis_core.field.CM31.add m0 c2
  let c4 ← aspis_core.field.CM31.sub m2 m0
  let c5 ← aspis_core.field.CM31.sub c4 m1
  ok { c0 := c3, c1 := c5 }
-- END GENERATED
end V7Tag73CurrentHelpersOpaque

namespace AspisV8R17.GeneratedQM31Products
open Aeneas.Std V7Tag73CurrentHelpersOpaque RawReducer

def words (x : aspis_core.field.CM31) : WordPair := (x.a.val,x.b.val)
def qmWords (x : aspis_core.field.QM31) := (words x.c0,words x.c1)

private theorem cm_add (x y : aspis_core.field.CM31)
    (hx : GeneratedCM31Linear.Canonical x) (hy : GeneratedCM31Linear.Canonical y) :
    ∃ z, aspis_core.field.CM31.add x y = .ok z ∧
      GeneratedCM31Linear.Canonical z ∧ words z = addWords (words x) (words y) := by
  obtain ⟨z, ez, cz, va, vb⟩ := GeneratedCM31Linear.generated_add_words x y hx hy
  exact ⟨z, ez, cz, Prod.ext va vb⟩

private theorem cm_sub (x y : aspis_core.field.CM31)
    (hx : GeneratedCM31Linear.Canonical x) (hy : GeneratedCM31Linear.Canonical y) :
    ∃ z, aspis_core.field.CM31.sub x y = .ok z ∧
      GeneratedCM31Linear.Canonical z ∧ words z = subWords (words x) (words y) := by
  obtain ⟨z, ez, cz, va, vb⟩ := GeneratedCM31Linear.generated_sub_words x y hx hy
  exact ⟨z, ez, cz, Prod.ext va vb⟩

private theorem cm_mul (x y : aspis_core.field.CM31)
    (hx : GeneratedCM31Linear.Canonical x) (hy : GeneratedCM31Linear.Canonical y) :
    ∃ z, aspis_core.field.CM31.mul x y = .ok z ∧
      GeneratedCM31Linear.Canonical z ∧ words z = mulWords (words x) (words y) := by
  obtain ⟨z, ez, va, vb, ca, cb⟩ := GeneratedCM31Mul.generated_mul_words x y hx.1 hx.2 hy.1 hy.2
  exact ⟨z, ez, ⟨ca,cb⟩, Prod.ext va vb⟩

private theorem cm_r (x : aspis_core.field.CM31) (hx : GeneratedCM31Linear.Canonical x) :
    ∃ z, aspis_core.field.mul_by_r x = .ok z ∧
      GeneratedCM31Linear.Canonical z ∧ words z = rWords (words x) := by
  obtain ⟨z, ez, cz, va, vb⟩ := GeneratedMulByR.generated_words x hx
  exact ⟨z, ez, cz, Prod.ext va vb⟩

theorem generated_mul_words (x y : aspis_core.field.QM31)
    (hx : GeneratedQM31Scalar.Canonical x) (hy : GeneratedQM31Scalar.Canonical y) :
    ∃ z, aspis_core.field.QM31.mul x y = .ok z ∧ GeneratedQM31Scalar.Canonical z ∧
      qmWords z = qmMulWords (qmWords x) (qmWords y) := by
  obtain ⟨m0, e0, c0, v0⟩ := cm_mul x.c0 y.c0 hx.1 hy.1
  obtain ⟨m1, e1, c1, v1⟩ := cm_mul x.c1 y.c1 hx.2 hy.2
  obtain ⟨a, ea, ca, va⟩ := cm_add x.c0 x.c1 hx.1 hx.2
  obtain ⟨b, eb, cb, vb⟩ := cm_add y.c0 y.c1 hy.1 hy.2
  obtain ⟨m2, e2, c2, v2⟩ := cm_mul a b ca cb
  obtain ⟨r, er, cr, vr⟩ := cm_r m1 c1
  obtain ⟨lo, el, cl, vl⟩ := cm_add m0 r c0 cr
  obtain ⟨d, ed, cd, vd⟩ := cm_sub m2 m0 c2 c0
  obtain ⟨hi, eh, ch, vh⟩ := cm_sub d m1 cd c1
  refine ⟨⟨lo,hi⟩, ?_, ⟨cl,ch⟩, ?_⟩
  · simp only [aspis_core.field.QM31.mul, e0, e1, ea, eb, e2, er, el, ed, eh, bind_tc_ok]
  · change (words lo, words hi) = _
    simp only [vl, vh, vd, vr, v2, va, vb, v0, v1, qmMulWords, qmWords]

theorem generated_square_words (x : aspis_core.field.QM31)
    (hx : GeneratedQM31Scalar.Canonical x) :
    ∃ z, aspis_core.field.QM31.square x = .ok z ∧ GeneratedQM31Scalar.Canonical z ∧
      qmWords z = qmSquareWords (qmWords x) := by
  obtain ⟨a, ea, ca, va⟩ := cm_mul x.c0 x.c0 hx.1 hx.1
  obtain ⟨b, eb, cb, vb⟩ := cm_mul x.c1 x.c1 hx.2 hx.2
  have esa := GeneratedCM31SquareNormalized.generated_square_eq_mul_self x.c0 hx.1.1 hx.1.2
  have esb := GeneratedCM31SquareNormalized.generated_square_eq_mul_self x.c1 hx.2.1 hx.2.2
  obtain ⟨r, er, cr, vr⟩ := cm_r b cb
  obtain ⟨lo, el, cl, vl⟩ := cm_add a r ca cr
  obtain ⟨m, em, cm, vm⟩ := cm_mul x.c0 x.c1 hx.1 hx.2
  obtain ⟨hi, eh, ch, vh⟩ := cm_add m m cm cm
  refine ⟨⟨lo,hi⟩, ?_, ⟨cl,ch⟩, ?_⟩
  · simp only [aspis_core.field.QM31.square, esa, esb, ea, eb, er, el, em,
      aspis_core.field.CM31.double, eh, bind_tc_ok]
  · change (words lo, words hi) = _
    simp only [vl, vh, vr, va, vb, vm, qmSquareWords, qmWords]

#print axioms generated_mul_words
#print axioms generated_square_words
end AspisV8R17.GeneratedQM31Products
