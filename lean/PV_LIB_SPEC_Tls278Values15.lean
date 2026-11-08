import PV_LIB_SPEC_TlsAt63
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Tls278Values15
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen

def token : Data := PV_THR2_RunTlsErrorCompleted.callee
def value (address : Address) : Data :=
  (PV_FN_THREAD_f170.SourceTlsValue.resultOk PV_LIB_SPEC_FrozenABI.resultType address).encode

theorem pure (p : Parameters) (w : OWNER) (address : Address) :
    PV_LIB_SPEC_SparseRuntime.pureValue (runtime p).carrier (runtime p).control w token
      [PV_LIB_SPEC_Tls277Native15.value address,PV_LIB_SPEC_Tls278Lift15.error] =
    some (value address) := by
  have variant : (runtime p).control.variant (PV_LIB_SPEC_Tls277Native15.value address) = some 1 := rfl
  have field : (runtime p).carrier.field (PV_LIB_SPEC_Tls277Native15.value address) 0 =
      some (PV_LIB_SPEC_Tls277Native15.pointer address) := rfl
  have deref : (runtime p).carrier.dereference w (PV_LIB_SPEC_Tls277Native15.pointer address) = some address := by
    simp only [PV_LIB_SPEC_Tls277Native15.pointer,runtime,PV_THR2_OwnInitExactReturnedCases.carrier,
      PV_THR2_EntryDynamic.carrier,PV_THR2_Scalars.carrier,
      PV_STX2_TypedReferences.carrier,PV_STX2_TypedReferences.roundtrip]
  unfold PV_LIB_SPEC_SparseRuntime.pureValue
  simp only [show PV_THR2_OffPath.functionId token=some 278 from rfl,variant,field,deref,Option.bind_some]
  rfl

/-- Exact declared278 value facets: result is Ok and the same source pointer
is retained. This is independent of physical-stack data or future execution. -/
theorem fields (p : Parameters) (w : OWNER) (address : Address) :
    (runtime p).control.variant (value address) = some 0 ∧
    (runtime p).carrier.field (value address) 0 = some
      (PV_LIB_SPEC_Tls277Native15.pointer address) ∧
    (runtime p).carrier.dereference w (PV_LIB_SPEC_Tls277Native15.pointer address) = some address := by
  refine ⟨rfl,rfl,?_⟩
  simp only [PV_LIB_SPEC_Tls277Native15.pointer,runtime,PV_THR2_OwnInitExactReturnedCases.carrier,
    PV_THR2_EntryDynamic.carrier,PV_THR2_Scalars.carrier,
    PV_STX2_TypedReferences.carrier,PV_STX2_TypedReferences.roundtrip]

#print axioms token
#print axioms value
#print axioms pure
#print axioms fields
end PV_LIB_SPEC_Tls278Values15
