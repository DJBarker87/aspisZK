import NNG_InvokeGraph094
import NNG_InstalledCalls094
import NNG_Tree094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_StateOccurrences094
open Aeneas Aeneas.Std Result NMT_tx1 NMT_CallTree NNG_Carriers094 NNG_StateCalls094

theorem accumulator (env : RSL.Env) (variant : transport.Variant) :
 LIB_Instances.VL.accNew.run () env
  (NNG_Observed136.observation (port toT15) (NNG_Events094.events env)
   (NNG_Tree094.NNG_call_10 (NNG_InstalledCalls094.calls env).c10 variant)) := by
 unfold NNG_Tree094.NNG_call_10
 rw [NNG_InvokeGraph094.observation,NNG_Events094.silent env _ _ _ (by decide) (by decide) (by decide)]
 exact accNew_graph env
#print axioms accumulator

theorem weights (env : RSL.Env) (a : verifier.Accumulator)
 (domain : LIBC_WeightsNew.Domain (toT15 a)) :
 LIB_Instances.VL.weightsNew.run (toT15 a) env
  (NNG_Observed136.observation (port toT13) (NNG_Events094.events env)
   (NNG_Tree094.NNG_call_8 (NNG_InstalledCalls094.calls env).c8 a.weights.deref)) := by
 unfold NNG_Tree094.NNG_call_8
 rw [NNG_InvokeGraph094.observation,NNG_Events094.silent env _ _ _ (by decide) (by decide) (by decide)]
 exact weightsNew_graph env a domain
#print axioms weights
end AspisR1.NNG_StateOccurrences094
