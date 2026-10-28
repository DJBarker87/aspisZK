import R1Z.PV_RDB2C_PV_B2_D_FromLimbs
set_option autoImplicit false
namespace PV_B2_D_MulQm31Total
open Aeneas Aeneas.Std Result PV_B2_251c1
abbrev E := aspis_core.field.wide_exact.WideExact
abbrev Q := aspis_core.field.QM31
namespace V
open PV_B2_C_251FieldValue
def norm (q : Q) : Q :=
  ⟨⟨aspis_core.field.ct.reduce64 (UScalar.cast .U64 q.c0.a),
     aspis_core.field.ct.reduce64 (UScalar.cast .U64 q.c0.b)⟩,
   ⟨aspis_core.field.ct.reduce64 (UScalar.cast .U64 q.c1.a),
     aspis_core.field.ct.reduce64 (UScalar.cast .U64 q.c1.b)⟩⟩
def value (x : E) (q : Q) : E :=
  ⟨aspis_core.field.QM31.mul x.c0 (norm q),aspis_core.field.QM31.mul x.c1 (norm q)⟩
end V

theorem source (x : E) (q : Q) : host_weights.mul_qm31 x q = ok (V.value x q) := by
  let a := PV_B2_C_251FieldValue.aspis_core.field.QM31.mul x.c0 (V.norm q)
  let b := PV_B2_C_251FieldValue.aspis_core.field.QM31.mul x.c1 (V.norm q)
  have ha := PV_B2_D_QuarticCanonical.qmul x.c0 (V.norm q)
  have hb := PV_B2_D_QuarticCanonical.qmul x.c1 (V.norm q)
  have he := PV_B2_D_FromLimbs.source a b ha hb
  simp only [host_weights.mul_qm31,PV_B2_C_251FieldTotal.ct_reduce64,
    PV_B2_C_251FieldTotal.QM31_mul,aspis_core.field.wide_exact.WideExact.impl.c0,
    aspis_core.field.wide_exact.WideExact.impl.c1,lift,bind_tc_ok]
  change (aspis_core.field.wide_exact.WideExact.from_limbs
    (PV_B2_D_FromLimbs.limbs a b) >>= core.option.Option.unwrap) = ok (⟨a,b⟩ : E)
  rw [he]
  rfl
#print axioms source
end PV_B2_D_MulQm31Total
