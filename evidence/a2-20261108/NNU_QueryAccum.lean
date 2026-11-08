import NNU_QueryLoops
import NNU_QueryFieldWide
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_QueryAccum
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody NNH_Run5bQuerySlots
variable (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)

theorem slots : NNU_QueryLoops.Slots (actual m env err r) model := by
 constructor <;> rfl

theorem sum (x y : aspis_core.field.wide_exact.WideExact) :
 (actual m env err r).op2 x y = model.op2 x y := by
 change SAQ_Arithmetic.add x y = NBO_FieldSemantics.add x y
 exact NNU_QueryFieldWide.add x y

theorem product (x : aspis_core.field.wide_exact.WideExact) (q : aspis_core.field.QM31)
 (hq : NBF_PowerStep.Canonical q) : (actual m env err r).op3 x q = model.op3 x q := by
 change SAQ_MixedSource.mulE x q = NBO_FieldSemantics.product x q
 exact NNU_QueryFieldWide.mixed x q hq

theorem power (x y : aspis_core.field.QM31) :
 (actual m env err r).op9 x y = model.op9 x y := by
 change SAQ_Arithmetic.mulK x y = NBO_FieldSemantics.power x y
 exact NNU_QueryFieldCarriers.mulQ x y

theorem source (p : verifier.Prepared) (a : verifier.Accumulator) (node : U32)
 (value : aspis_core.field.wide_exact.WideExact) (pending : verifier.BatchedWeights)
 (hq : NBF_PowerStep.Canonical a.power) :
 verifier.accumulate_batched_with_node (actual m env err r) p a node value pending =
 verifier.accumulate_batched_with_node model p a node value pending := by
 have s:=slots m env err r
 unfold verifier.accumulate_batched_with_node
 simp only [s.zero,s.one,NNU_QueryLoops.basisLoop _ _ s,NNU_QueryLoops.rowLoop _ _ s,
  product m env err r value a.power hq,sum m env err r,power m env err r,s.trace]
#print axioms slots
#print axioms sum
#print axioms product
#print axioms power
#print axioms source
end AspisR1.NNU_QueryAccum
end
