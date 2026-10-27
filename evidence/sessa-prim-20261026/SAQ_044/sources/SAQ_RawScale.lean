import CurrentWideField
import CurrentWideQMMulM31V5
import R17CurrentM31Semantics
import WideTower
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.SAQ_RawScale
open AspisR1CurrentWide AspisR1CurrentWide.Proof
abbrev MExact := AspisR1.ExtractedCurrentQM31Exact.M31Exact
private def qmScalarEmbedding (s : field.M31) : ExactQM :=
  ⟨⟨(s.val : MExact), (0 : MExact)⟩, ⟨(0 : MExact), (0 : MExact)⟩⟩
def wideScalarEmbedding (s : field.M31) : AspisWideTower.WideExact :=
  ⟨qmScalarEmbedding s, 0⟩


theorem wideScalarEmbedding_eq_algebraMap (s : field.M31) :
    wideScalarEmbedding s =
      algebraMap MExact AspisWideTower.WideExact
        (R17CurrentM31Semantics.decode s) := by
  simp [wideScalarEmbedding, qmScalarEmbedding,
    R17CurrentM31Semantics.decode, R17CurrentM31Semantics.P,
    AspisV8R15.ExactTowerBase.QM31Exact,
    AspisV8R15.ExactTowerBase.CM31Exact,
    AspisV8R15.ExactTowerBase.M31Exact]
  rfl

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem wide_mul_m31_success (x z : E) (s : field.M31)
    (h : field.wide_exact.WideExact.mul_m31 x s = .ok z) :
    CanonicalWide z ∧ decodeWide z = decodeWide x * wideScalarEmbedding s := by
  unfold field.wide_exact.WideExact.mul_m31 at h
  rcases bind_ok_inv h with ⟨i, hi, h⟩
  rcases bind_ok_inv h with ⟨q, hq, h⟩
  rcases bind_ok_inv h with ⟨q1, hq1, h⟩
  have he : ({c0 := q, c1 := q1} : E) = z := Result.ok.inj h
  subst z
  have hq0 := qm_mul_m31_success x.c0 i q hq
  have hq1' := qm_mul_m31_success x.c1 i q1 hq1
  have hden : field.P.val ≠ 0 := by norm_num [field.P]
  obtain ⟨irem, hrem, hremVal⟩ := Aeneas.Std.WP.spec_imp_exists (UScalar.rem_spec s hden)
  have hie : i = irem := Result.ok.inj (hi.symm.trans hrem)
  subst irem
  have hpExact : field.P.val = AspisV8R15.ExactTowerBase.P := by
    norm_num [field.P, AspisV8R15.ExactTowerBase.P]
  have hbase : (i.val : MExact) = (s.val : MExact) := by
    change (i.val : ZMod AspisV8R15.ExactTowerBase.P) =
      (s.val : ZMod AspisV8R15.ExactTowerBase.P)
    rw [hremVal, hpExact, ZMod.natCast_mod]
  have hscalar : wideScalarEmbedding i = wideScalarEmbedding s := by
    ext <;> simp [wideScalarEmbedding, qmScalarEmbedding, hbase]
  refine ⟨⟨hq0.1,hq1'.1⟩, ?_⟩
  rw [← hscalar]
  apply QuadraticAlgebra.ext
  · have hq0r := hq0.2
    have heq : decodeQM q = decodeQM x.c0 * qmScalarEmbedding i := by
      change decodeQM q = decodeQM x.c0 * qmScalarEmbedding i at hq0r
      exact hq0r
    rw [QuadraticAlgebra.re_mul]
    simpa [decodeWide, wideScalarEmbedding] using heq
  · have hq1r := hq1'.2
    have heq : decodeQM q1 = decodeQM x.c1 * qmScalarEmbedding i := by
      change decodeQM q1 = decodeQM x.c1 * qmScalarEmbedding i at hq1r
      exact hq1r
    rw [QuadraticAlgebra.im_mul]
    simpa [decodeWide, wideScalarEmbedding] using heq

theorem wide_mul_m31_success_algebraMap (x z : E) (s : field.M31)
    (h : field.wide_exact.WideExact.mul_m31 x s = .ok z) :
    CanonicalWide z ∧ decodeWide z = decodeWide x *
      algebraMap MExact AspisWideTower.WideExact (R17CurrentM31Semantics.decode s) := by
  obtain ⟨hc,hv⟩ := wide_mul_m31_success x z s h
  refine ⟨hc, ?_⟩
  rw [← wideScalarEmbedding_eq_algebraMap]
  exact hv

#print axioms qmScalarEmbedding
#print axioms wideScalarEmbedding
#print axioms wide_mul_m31_success
#print axioms wide_mul_m31_success_algebraMap
end AspisR1.SAQ_RawScale
