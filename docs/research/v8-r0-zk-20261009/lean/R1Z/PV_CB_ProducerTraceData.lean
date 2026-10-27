import R1Z.PV_CB_ProducerSelected
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_ProducerTraceData
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_ProducerLimb
variable [ExternalTypes]

/-- Plain numerical trace invariant, independent of compressor outputs. -/
def Valid (trace : Trace) : Prop :=
  (∀ column ∈ trace.stable.c1.val, ∀ word ∈ column.val, PV_CB_CanonicalM31.Valid word) ∧
  (∀ column ∈ trace.late.val, ∀ word ∈ column.val, PV_CB_CanonicalM31.Valid word)

theorem reads (trace : Trace) (valid : Valid trace) : TraceReads trace :=
  ⟨PV_CB_ProducerRead.reads (Array.to_slice trace.stable.c1) valid.1,
   PV_CB_ProducerRead.reads (Array.to_slice trace.late) valid.2⟩

theorem successful_array (ops : ExternalFuns) (trace : Trace) (input : PV_CB_ProducerTuple.Tuple)
    (vt : Valid trace) (vo : PV_CB_CanonicalArrays.Valid OffsetValid input.limbs)
    (values : Array U32 16#usize)
    (produced : @host_semantic.copy_tuple_values _ (PV_CurrentScaleInstall.selected ops)
      trace input = ok (.Ok values)) :
    PV_CB_CanonicalArrays.Valid PV_CB_CanonicalM31.Valid values :=
  PV_CB_ProducerSelected.successful_array ops trace input (reads trace vt) vo values produced
#print axioms reads
#print axioms successful_array
end R1Z.PV_CB_ProducerTraceData
