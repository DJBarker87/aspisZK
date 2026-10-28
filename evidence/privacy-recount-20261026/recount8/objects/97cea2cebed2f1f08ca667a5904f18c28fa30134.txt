import R1Z.PV_Join_OwnedStep5_04
import R1Z.ProverRwP7CurrentCtBridge
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_OwnedCtBridge5
open Aeneas Aeneas.Std Result
namespace S
abbrev subp := PV_Join_Direct5Source.aspis_core.field.ct.subtract_p
abbrev reduce := PV_Join_Direct5Source.aspis_core.field.ct.reduce64
abbrev add := PV_Join_Direct5Source.aspis_core.field.ct.add
abbrev sub := PV_Join_Direct5Source.aspis_core.field.ct.sub
end S

theorem subtract (x : U32) : S.subp x = ProverRwSuccessCtSubtract.source x := by
  simp only [S.subp,PV_Join_Direct5Source.aspis_core.field.ct.subtract_p,
    PV_Join_Direct5Source.aspis_core.field.P,ProverRwSuccessCtSubtract.source,
    ProverRwSuccessNativePorts.aspis_core.field.ct.subtract_p,
    ProverRwSuccessNativePorts.aspis_core.field.P,AspisR1ProducerRelease47.field.P,
    lift,bind_tc_ok]

theorem reduce (x : U64) : S.reduce x = AspisR1ProducerRelease47.field.reduce_u64 x := by
  rw [← ProverRwSuccessCtReduce.reduce]
  simp only [S.reduce,PV_Join_Direct5Source.aspis_core.field.ct.reduce64,
    ProverRwSuccessCtReduce.source,ProverRwSuccessNativePorts.aspis_core.field.ct.reduce64,
    PV_Join_Direct5Source.aspis_core.field.P,ProverRwSuccessNativePorts.aspis_core.field.P,
    AspisR1ProducerRelease47.field.P,lift,bind_tc_ok,subtract]

theorem add (a b : U32) : S.add a b = AspisR1ProducerRelease47.field.M31.add a b := by
  simp only [S.add,PV_Join_Direct5Source.aspis_core.field.ct.add,lift,bind_tc_ok,
    subtract,ProverRwSuccessCtSubtract.subtract,AspisR1ProducerRelease47.field.M31.add,
    ProverRwSuccessCtSubtract.p,ProverRwP7CurrentCtApi.add,ProverRwP7CurrentCtApi.sub]
  split <;> simp_all only [if_pos,if_neg]

theorem sub (a b : U32) : S.sub a b = AspisR1ProducerRelease47.field.M31.sub a b := by
  simp only [S.sub,PV_Join_Direct5Source.aspis_core.field.ct.sub,
    PV_Join_Direct5Source.aspis_core.field.P,lift,bind_tc_ok,
    subtract,ProverRwSuccessCtSubtract.subtract,AspisR1ProducerRelease47.field.M31.sub,
    ProverRwSuccessCtSubtract.p,AspisR1ProducerRelease47.field.P,
    ProverRwP7CurrentCtApi.add,ProverRwP7CurrentCtApi.sub]
  split <;> simp_all only [if_pos,if_neg]

#print axioms subtract
#print axioms reduce
#print axioms add
#print axioms sub
end R1Z.PV_Join_OwnedCtBridge5
