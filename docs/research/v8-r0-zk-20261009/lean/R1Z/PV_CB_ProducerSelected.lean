import R1Z.PV_CB_ProducerContext
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_ProducerSelected
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_ProducerLimb
variable [ExternalTypes]

theorem tuple (ops : ExternalFuns) (trace : Trace) (input : PV_CB_ProducerTuple.Tuple)
    (vt : TraceReads trace)
    (vo : PV_CB_CanonicalArrays.Valid OffsetValid input.limbs) :
    PV_CB_ProducerPost.Good (PV_CB_CanonicalArrays.Valid PV_CB_CanonicalM31.Valid)
      (@host_semantic.copy_tuple_values _ (PV_CurrentScaleInstall.selected ops) trace input) := by
  rw [PV_CB_ProducerContext.tuple_congr (PV_CurrentScaleInstall.selected ops)
    (ProverRwDictionaryScalar.selected ops) (by rfl) (by rfl)]
  exact PV_CB_ProducerTuple.tuple ops trace input vt vo

/-- Numerical array invariant at the actual callback-producing function.
Trace and offset representation invariants remain explicit input conditions. -/
theorem successful_array (ops : ExternalFuns) (trace : Trace) (input : PV_CB_ProducerTuple.Tuple)
    (vt : TraceReads trace)
    (vo : PV_CB_CanonicalArrays.Valid OffsetValid input.limbs)
    (values : Array U32 16#usize)
    (produced : @host_semantic.copy_tuple_values _ (PV_CurrentScaleInstall.selected ops)
      trace input = ok (.Ok values)) :
    PV_CB_CanonicalArrays.Valid PV_CB_CanonicalM31.Valid values :=
  tuple ops trace input vt vo values produced
#print axioms tuple
#print axioms successful_array
end R1Z.PV_CB_ProducerSelected
