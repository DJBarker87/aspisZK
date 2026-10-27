import XRy_QueryTransport
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
 simp only [bind_tc_ok]
 trace_state

#print axioms embed
#print AspisS1M31Embedding.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
#print AspisS1M31Embedding.aspis_core.field.wide_exact.WideExact.from_qm31
#print AspisS1M31Embedding.aspis_core.field.wide_exact.canonical_qm31
end XRy_QueryEmbedding
