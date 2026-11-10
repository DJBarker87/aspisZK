import NPH_R22Installers
import NPH_R22Producers
import CurrentWideMulCanonical
import NFN_GeometryPart03

/-! NPH_ (R22, run of 2026-11-10 evening, step D): Qm31ArithmeticProbe (QA) sites added by the
tightened screen (NPH_sites_scan2.py). The screen counts a site only when its body reaches a
DOMAIN-ONLY QA kernel (M31.add/sub, CM31.mul). The SAF_/SAP_ Outcome families,
Port4C_InverseExecution/OwnedInverse, SAQ_Inverse.source, NFN_NEW_GeometryPrefix.leaves,
S7Kani2PrefixLoop.prefixes_owned, S7Kani3BasisOuter.basis_levels_owned/levels and
Tx1Q_Endpoint.WhenBound call only QA M31.mul, which is TOTAL for every input (NPH_R22FieldCopies);
they impose no precondition and leave the checklist.
- CurrentWideMulCanonical hand-written copies over the QA tower: QM31.sub, wide_exact.mul_u and
  wide_exact.WideExact.mul map W inputs to an ok W output.
- NFN_NEB_GeometryPrimitives.install: its M31 slots op7–op10 satisfy GeometryM31W (as
  SAQ_Geometry.install); op14/op15 use NFN_NEA_FieldProduct.ops and are not covered here.
- NFN_NEW_GeometryPolynomial.cohort: ok with W output for EVERY input (mul first).
Standard axioms; no ops interface or merged module is changed. -/
set_option autoImplicit false
namespace AspisR1.NPH_R22JoinQA
open Aeneas Aeneas.Std Result AspisR1.NPH_R22Installers AspisR1.NPH_R22Producers

abbrev CWMW (x : AspisR1CurrentWideMul.field.wide_exact.WideExact) : Prop := QA_WQ x.c0 ∧ QA_WQ x.c1

theorem CWM_QM31_sub_W (a b : AspisR1Qm31ArithmeticProbe.field.QM31) (ha : QA_WQ a) (hb : QA_WQ b) :
    ∃ z, AspisR1CurrentWideMul.field.QM31.sub a b = ok z ∧ QA_WQ z := by
  obtain ⟨c, hc, wc⟩ := QA_CM31_sub_weak a.c0 b.c0 ha.1 hb.1
  obtain ⟨c1, hc1, wc1⟩ := QA_CM31_sub_weak a.c1 b.c1 ha.2 hb.2
  exact ⟨({ c0 := c, c1 := c1 } : AspisR1Qm31ArithmeticProbe.field.QM31),
    by simp only [AspisR1CurrentWideMul.field.QM31.sub, AspisR1CurrentWideMul.field.cm.CM31.sub, hc, hc1, bind_tc_ok], wc, wc1⟩

theorem CWM_mul_u_W (q : AspisR1Qm31ArithmeticProbe.field.QM31) (hq : QA_WQ q) :
    ∃ z, AspisR1CurrentWideMul.field.wide_exact.mul_u q = ok z ∧ QA_WQ z := by
  obtain ⟨c, hc, wc⟩ := QA_mul_by_r_weak q.c1 hq.2
  exact ⟨({ c0 := c, c1 := q.c0 } : AspisR1Qm31ArithmeticProbe.field.QM31),
    by simp only [AspisR1CurrentWideMul.field.wide_exact.mul_u, AspisR1CurrentWideMul.field.mul_by_r, hc, bind_tc_ok], wc, hq.1⟩

theorem CWM_WideExact_mul_W (x y : AspisR1CurrentWideMul.field.wide_exact.WideExact) (hx : CWMW x) (hy : CWMW y) :
    ∃ z, AspisR1CurrentWideMul.field.wide_exact.WideExact.mul x y = ok z ∧ CWMW z := by
  obtain ⟨ac, hac, vac⟩ := QA_QM31_mul_weak x.c0 y.c0 hx.1 hy.1
  obtain ⟨bd, hbd, vbd⟩ := QA_QM31_mul_weak x.c1 y.c1 hx.2 hy.2
  obtain ⟨q, hq, vq⟩ := QA_QM31_add_weak x.c0 x.c1 hx.1 hx.2
  obtain ⟨q1, hq1, vq1⟩ := QA_QM31_add_weak y.c0 y.c1 hy.1 hy.2
  obtain ⟨cr, hcr, vcr⟩ := QA_QM31_mul_weak q q1 vq vq1
  obtain ⟨q2, hq2, vq2⟩ := CWM_mul_u_W bd vbd
  obtain ⟨q3, hq3, vq3⟩ := QA_QM31_add_weak ac q2 vac vq2
  obtain ⟨q4, hq4, vq4⟩ := CWM_QM31_sub_W cr ac vcr vac
  obtain ⟨q5, hq5, vq5⟩ := CWM_QM31_sub_W q4 bd vq4 vbd
  refine ⟨({ c0 := q3, c1 := q5 } : AspisR1CurrentWideMul.field.wide_exact.WideExact), ?_, vq3, vq5⟩
  simp only [AspisR1CurrentWideMul.field.wide_exact.WideExact.mul, AspisR1CurrentWideMul.field.QM31.mul,
    AspisR1CurrentWideMul.field.QM31.add, hac, hbd, hq, hq1, hcr, hq2, hq3, hq4, hq5, bind_tc_ok]

theorem NFN_install_W {C : Type} (ops : Port3_NativeGeometryBody.Ops C) :
    GeometryM31W (NFN_NEB_GeometryPrimitives.install ops) :=
  ⟨const1, QA_sub_pres, QA_mul_pres, QA_double_pres⟩

theorem cohort_W (x : U32) : ∃ z, NFN_NEW_GeometryPolynomial.cohort x = ok z ∧ W z := by
  obtain ⟨p, hp, vp⟩ := AspisR1.NPH_R22FieldRef.refMul_total x x
  have hp' : AspisR1Qm31ArithmeticProbe.field.M31.mul x x = ok p := by
    rw [AspisR1.NPH_R22FieldCopies.QA_M31_mul_eq]; exact hp
  obtain ⟨d, hd, vd⟩ := QA_double_pres p (Nat.le_of_lt vp)
  obtain ⟨z, hz, vz⟩ := QA_sub_pres d 1#u32 vd (by unfold W; first | decide | simp)
  exact ⟨z, by simp only [NFN_NEW_GeometryPolynomial.cohort, hp', hd, hz, bind_tc_ok], vz⟩

#print axioms CWM_QM31_sub_W
#print axioms CWM_mul_u_W
#print axioms CWM_WideExact_mul_W
#print axioms NFN_install_W
#print axioms cohort_W
end AspisR1.NPH_R22JoinQA
