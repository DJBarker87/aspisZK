import NMS_RSLPoolCarriers
import NMS_Interpreted
set_option autoImplicit false
noncomputable section
namespace NMS_GetterStopDifference
open Aeneas Aeneas.Std Result AdapterRw
/-- Exact source support: a stopped clone is a stopped getter, with no
invented returned ProgramError. This is conditional on the local std call's
reply; it does not assert that a particular deployed execution stops. -/
theorem clone_stop (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount)
 (error : solana_program_error.ProgramError) (stop : Error)
 (stored : a.bytes = .Err error) (clone : ops.op35 error = .fail stop) :
 NMS_Emitted.get ops a = .fail stop := by
 simp only [NMS_Emitted.get,stored,clone,bind_tc_fail]

/-- Canonical pure data semantics has no abort observation at all. -/
theorem canonical_no_abort (a : RSL.OwnedAccount) (env : RSL.Env) (events : List RSL.Event) :
 ¬ RSL.RS.ofExcept a.data env ⟨.abort,events⟩ := by
 intro run
 have impossible := congrArg RSL.Obs.exit run
 cases impossible

/-- The two getter interpretations differ whenever that SAME clone stops.
No generic allocation-success or clone-totality premise is licensed. -/
theorem not_simulated (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount)
 (error : solana_program_error.ProgramError) (stop : Error)
 (stored : a.bytes = .Err error) (clone : ops.op35 error = .fail stop) :
 ¬ NMS_Interpreted.Simulates (NMS_RSLError.reply NMS_RSLScalars.bytes)
   (NMS_Interpreted.liftResult (NMS_Emitted.get ops a))
   (RSL.RS.ofExcept (NMS_RSLPoolCarriers.account a).data) := by
 intro simulation
 have actual : NMS_Interpreted.liftResult (NMS_Emitted.get ops a)
   RSL.env0 ⟨.abort,[]⟩ := by
   rw [clone_stop ops a error stop stored clone]
   rfl
 exact canonical_no_abort _ RSL.env0 [] (simulation RSL.env0 _ actual)
#print axioms clone_stop
#print axioms canonical_no_abort
#print axioms not_simulated
end NMS_GetterStopDifference
