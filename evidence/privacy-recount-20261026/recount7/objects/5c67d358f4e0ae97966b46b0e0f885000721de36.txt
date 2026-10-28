import R1Z.ProverRwP7CurrentCtApi
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP7CurrentCtBridge
open Aeneas Aeneas.Std Result
namespace S
abbrev subtract := ProverRwP7CurrentFieldSource.aspis_core.field.ct.subtract_p
abbrev reduce := ProverRwP7CurrentFieldSource.aspis_core.field.ct.reduce64
abbrev add := ProverRwP7CurrentFieldSource.aspis_core.field.ct.add
abbrev sub := ProverRwP7CurrentFieldSource.aspis_core.field.ct.sub
end S

theorem subtract_source (x : U32) : S.subtract x = ProverRwSuccessCtSubtract.source x := by
  simp only [S.subtract,ProverRwP7CurrentFieldSource.aspis_core.field.ct.subtract_p,
    ProverRwSuccessCtSubtract.source,ProverRwSuccessNativePorts.aspis_core.field.ct.subtract_p,
    ProverRwP7CurrentFieldSource.aspis_core.field.P,ProverRwSuccessNativePorts.aspis_core.field.P,
    AspisR1ProducerRelease47.field.P,lift,bind_tc_ok]

theorem reduce_source (x : U64) : S.reduce x = AspisR1ProducerRelease47.field.reduce_u64 x := by
  rw [← ProverRwSuccessCtReduce.reduce]
  simp only [S.reduce,ProverRwP7CurrentFieldSource.aspis_core.field.ct.reduce64,
    ProverRwSuccessCtReduce.source,ProverRwSuccessNativePorts.aspis_core.field.ct.reduce64,
    ProverRwP7CurrentFieldSource.aspis_core.field.P,ProverRwSuccessNativePorts.aspis_core.field.P,
    AspisR1ProducerRelease47.field.P,lift,bind_tc_ok,subtract_source]

theorem add_source (a b : U32) : S.add a b = AspisR1ProducerRelease47.field.M31.add a b := by
  simp only [S.add,ProverRwP7CurrentFieldSource.aspis_core.field.ct.add,
    lift,bind_tc_ok,subtract_source,ProverRwSuccessCtSubtract.subtract,
    AspisR1ProducerRelease47.field.M31.add,ProverRwSuccessCtSubtract.p,
    ProverRwP7CurrentCtApi.add,ProverRwP7CurrentCtApi.sub]
  split <;> simp_all only [if_pos,if_neg]

theorem sub_source (a b : U32) : S.sub a b = AspisR1ProducerRelease47.field.M31.sub a b := by
  simp only [S.sub,ProverRwP7CurrentFieldSource.aspis_core.field.ct.sub,
    ProverRwP7CurrentFieldSource.aspis_core.field.P,lift,bind_tc_ok,
    subtract_source,ProverRwSuccessCtSubtract.subtract,
    AspisR1ProducerRelease47.field.M31.sub,ProverRwSuccessCtSubtract.p,
    AspisR1ProducerRelease47.field.P,ProverRwP7CurrentCtApi.add,ProverRwP7CurrentCtApi.sub]
  split <;> simp_all only [if_pos,if_neg]
#print axioms subtract_source
#print axioms reduce_source
#print axioms add_source
#print axioms sub_source
end R1Z.ProverRwP7CurrentCtBridge
