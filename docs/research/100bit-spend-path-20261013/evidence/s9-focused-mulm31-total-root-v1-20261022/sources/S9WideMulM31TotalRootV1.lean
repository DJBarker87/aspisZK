import S3S9ConcreteFieldOpsV1
import CurrentWideMulM31V13

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1CurrentWide.Proof

/-- Four existing total U32 multiplication contracts construct this actual
source call's result. No successful-QM-call premise or input bound is needed. -/
theorem qm_mul_m31_total (x : field.QM31) (s : field.M31) :
    ∃ z, field.QM31.mul_m31 x s = .ok z := by
  let old := toQM x
  obtain ⟨a, ha, _hva, _hca⟩ :=
    AspisR1.ExtractedCurrentReducer.current_mul_mod old.c0.a s
  obtain ⟨b, hb, _hvb, _hcb⟩ :=
    AspisR1.ExtractedCurrentReducer.current_mul_mod old.c0.b s
  obtain ⟨c, hc, _hvc, _hcc⟩ :=
    AspisR1.ExtractedCurrentReducer.current_mul_mod old.c1.a s
  obtain ⟨d, hd, _hvd, _hcd⟩ :=
    AspisR1.ExtractedCurrentReducer.current_mul_mod old.c1.b s
  have haNew : field.M31.mul x.c0.a s = .ok a := by
    rw [m31_mul_same]; exact ha
  have hbNew : field.M31.mul x.c0.b s = .ok b := by
    rw [m31_mul_same]; exact hb
  have hcNew : field.M31.mul x.c1.a s = .ok c := by
    rw [m31_mul_same]; exact hc
  have hdNew : field.M31.mul x.c1.b s = .ok d := by
    rw [m31_mul_same]; exact hd
  refine ⟨⟨⟨a,b⟩,⟨c,d⟩⟩, ?_⟩
  simp only [field.QM31.mul_m31, field.CM31.mul_m31,
    haNew, hbNew, hcNew, hdNew, bind_tc_ok]

/-- Checked remainder and both QM multiplications construct the actual
WideExact source result for every stored input, not merely reached inputs. -/
theorem wide_mul_m31_total (x : E) (s : field.M31) :
    ∃ z, field.wide_exact.WideExact.mul_m31 x s = .ok z := by
  have hp : field.P.val ≠ 0 := by norm_num [field.P]
  obtain ⟨i, hi, _hiv⟩ := Aeneas.Std.WP.spec_imp_exists (UScalar.rem_spec s hp)
  obtain ⟨a, ha⟩ := qm_mul_m31_total x.c0 i
  obtain ⟨b, hb⟩ := qm_mul_m31_total x.c1 i
  refine ⟨⟨a,b⟩, ?_⟩
  simp only [field.wide_exact.WideExact.mul_m31, hi, ha, hb, bind_tc_ok]

end AspisR1CurrentWide.Proof

namespace AspisR1.S9WideMulM31TotalRootV1

abbrev W := AspisR1S9HelperP6.field.WideExact
abbrev M := AspisR1S9HelperP6.field.M31
open AspisR1S9CurrentFieldOpsV1

/-- Totality is unconditional on raw stored values, and is supplied to the
same concrete helper slot that the S9 loop executes. -/
theorem concrete_wideMulM31_total (x : W) (s : M) :
    ∃ z, AspisR1S9ConcreteFieldOpsV1.concreteFieldOps.wideMulM31 x s = .ok z := by
  obtain ⟨z, hz⟩ := AspisR1CurrentWide.Proof.wide_mul_m31_total (toE x) s
  refine ⟨fromE z, ?_⟩
  change actualWideMulM31 x s = .ok (fromE z)
  simp only [actualWideMulM31, hz, bind_tc_ok]

/-- The previous success-conditional exactness theorem now consumes the
constructed output; successful execution is no longer an antecedent. -/
theorem concrete_wideMulM31_total_exact (x : W) (s : M)
    (hx : Canonical x) :
    ∃ z, AspisR1S9ConcreteFieldOpsV1.concreteFieldOps.wideMulM31 x s = .ok z ∧
      Canonical z ∧ decode z = decode x * AspisR1CurrentWide.Proof.wideScalarEmbedding s := by
  obtain ⟨z, hz⟩ := concrete_wideMulM31_total x s
  refine ⟨z, hz, ?_⟩
  exact actualWideMulM31_success x z s hx hz

#print axioms AspisR1CurrentWide.Proof.qm_mul_m31_total
#print axioms AspisR1CurrentWide.Proof.wide_mul_m31_total
#print axioms concrete_wideMulM31_total
#print axioms concrete_wideMulM31_total_exact
end AspisR1.S9WideMulM31TotalRootV1
