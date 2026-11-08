import NNG_InvokeGraph094
import NNG_Tree094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_QueryOccurrence094
open Aeneas Aeneas.Std Result NMT_tx1 NMT_CallTree NNG_Carriers094

theorem source (env : RSL.Env) (s : NNG_Context094.Parent Unit)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (geo : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) (domain : LIBC_QueryLoop.Domain
  (LIB_Carriers.bytes s.proof,toT12 p,toT15 a,arr toT3 g,toT14 geo,toT13 pending,s.k.val)) :
 LIB_Instances.VL.queryLoop.run
  (LIB_Carriers.bytes s.proof,toT12 p,toT15 a,arr toT3 g,toT14 geo,toT13 pending,s.k.val) env
  (NNG_Observed136.observation (NNG_StateCalls094.port (fun r=>(toT15 r.1,toT13 r.2)))
   (NNG_Events094.events env) (NNG_Tree094.NNG_call_4 (NNG_InstalledCalls094.calls env).c4
    s.proof p a g s.observer geo pending s.k)) := by
 unfold NNG_Tree094.NNG_call_4
 rw [NNG_InvokeGraph094.observation,NNG_Events094.silent env _ _ _ (by decide) (by decide) (by decide)]
 exact NNG_StateCalls094.queryLoop_graph env s.proof p a g geo pending s.k domain
#print axioms source
end AspisR1.NNG_QueryOccurrence094
