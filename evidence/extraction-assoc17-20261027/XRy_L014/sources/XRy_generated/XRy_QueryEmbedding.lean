import XRy_QueryTransport
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
noncomputable section
namespace XRy_QueryEmbedding

theorem embed (x : U32) :
 aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 x =
 AspisS1M31Embedding.Total.embed x := by
 rfl

#print axioms embed
#print AspisS1M31Embedding.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
#print AspisS1M31Embedding.aspis_core.field.wide_exact.WideExact.from_qm31
#print AspisS1M31Embedding.aspis_core.field.wide_exact.WideExact.new
end XRy_QueryEmbedding
