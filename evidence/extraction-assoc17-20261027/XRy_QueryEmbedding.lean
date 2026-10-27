import XRy_Remainder
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
noncomputable section
namespace XRy_QueryEmbedding

theorem embed (x : U32) :
 aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 x =
 AspisS1M31Embedding.Total.embed x := by
 unfold aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
   aspis_core.field.wide_exact.WideExact.from_qm31
   aspis_core.field.wide_exact.WideExact.new
   XRn_Join_FieldExternal.canon
   AspisS1M31Embedding.Total.embed AspisS1M31Embedding.source_from_m31
   AspisS1M31Embedding.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
   AspisS1M31Embedding.aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.from_m31
   AspisS1M31Embedding.aspis_core.field.wide_exact.WideExact.from_qm31
   AspisS1M31Embedding.aspis_core.field.wide_exact.canonical_qm31
 simp only [AspisS1M31Embedding.aspis_core.field.CM31.Insts.Aspis_coreR0ScalarCodeField.from_m31,
   AspisS1M31Embedding.aspis_core.field.QM31.from_cm31,
   AspisS1M31Embedding.aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
   XRn_Join_FieldExternal.qzero,bind_tc_ok,bind_assoc_eq]
 have hz : 0#u32 % 2147483647#u32 = ok 0#u32 := by rfl
 simp only [AspisS1M31Embedding.aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.from_m31,
   AspisS1M31Embedding.aspis_core.field.CM31.from_m31,
   AspisS1M31Embedding.aspis_core.field.CM31.ZERO,
   AspisS1M31Embedding.aspis_core.field.QM31.ZERO,
   AspisS1M31Embedding.aspis_core.field.P,
   AspisS1M31Embedding.aspis_core.field.M31.ZERO,hz,bind_tc_ok,bind_assoc_eq]
 obtain ⟨z,hx,hp,hz⟩ := XRy_Remainder.canonical x
 simp only [hx,hz,bind_tc_ok]
 rfl

#print axioms embed
#print AspisS1M31Embedding.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
#print AspisS1M31Embedding.aspis_core.field.wide_exact.WideExact.from_qm31
#print AspisS1M31Embedding.aspis_core.field.wide_exact.canonical_qm31
end XRy_QueryEmbedding
