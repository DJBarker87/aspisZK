import R1Z.PV_RDB2E_ConcreteSoft
import R1Z.PV_RDB2E_Dispatch
import R1Z.PV_RDB2E_DispatchCallbacks
import R1Z.PV_RDB2E_FallbackArray4
import R1Z.PV_RDB2E_FallbackArray8
import R1Z.PV_RDB2E_FallbackArrayRead
import R1Z.PV_RDB2E_FallbackBlock
import R1Z.PV_RDB2E_FallbackBlockLinks
import R1Z.PV_RDB2E_FallbackBlockSwap
import R1Z.PV_RDB2E_FallbackBlockTotal
import R1Z.PV_RDB2E_FallbackCanonical
import R1Z.PV_RDB2E_FallbackConstants
import R1Z.PV_RDB2E_FallbackFeedForward
import R1Z.PV_RDB2E_FallbackHelpersTotal
import R1Z.PV_RDB2E_FallbackLanes
import R1Z.PV_RDB2E_FallbackMessage1
import R1Z.PV_RDB2E_FallbackMessage2
import R1Z.PV_RDB2E_FallbackRecurrence
import R1Z.PV_RDB2E_FallbackRotate
import R1Z.PV_RDB2E_FallbackRound
import R1Z.PV_RDB2E_FallbackRoundComplete
import R1Z.PV_RDB2E_FallbackRoundShape
import R1Z.PV_RDB2E_FallbackRoundTotal
import R1Z.PV_RDB2E_FallbackScalar
import R1Z.PV_RDB2E_FallbackSchedule
import R1Z.PV_RDB2E_FallbackScheduleRecurrence
import R1Z.PV_RDB2E_FallbackScheduleShape
import R1Z.PV_RDB2E_FallbackStateCodec
import R1Z.PV_RDB2E_FallbackTotal
import R1Z.PV_RDB2E_FromFn
import R1Z.PV_RDB2E_PointerOffsets
import R1Z.PV_RDB2E_ScalarSourceBridge
import R1Z.PV_RDB2E_ScalarTransport
import R1Z.PV_RDB2E_ShaBanks
import R1Z.PV_RDB2E_ShaCallback
import R1Z.PV_RDB2E_ShaHandles
import R1Z.PV_RDB2E_ShaScalar
import R1Z.PV_RDB2E_ShaSchedule
import R1Z.PV_RDB2E_ShaStage00
import R1Z.PV_RDB2E_ShaStage01
import R1Z.PV_RDB2E_ShaStage02
import R1Z.PV_RDB2E_ShaStage03
import R1Z.PV_RDB2E_ShaStage04
import R1Z.PV_RDB2E_ShaStage05
import R1Z.PV_RDB2E_ShaStage06
import R1Z.PV_RDB2E_ShaStage07
import R1Z.PV_RDB2E_ShaStage08
import R1Z.PV_RDB2E_ShaStage09
import R1Z.PV_RDB2E_ShaStage10
import R1Z.PV_RDB2E_ShaStage11
import R1Z.PV_RDB2E_ShaStage12
import R1Z.PV_RDB2E_ShaStage13
import R1Z.PV_RDB2E_ShaStage14
import R1Z.PV_RDB2E_ShaStage15
import R1Z.PV_RDB2E_ShaTypedFinal

/-! Independent source-projection cohort. The stopped sampler/R72 cone is not
imported. This is not a native whole-row or privacy-endpoint theorem. -/
namespace R1Z.PV_RDB2E_IndependentRoot
open Aeneas Aeneas.Std Result PV_RDB2E_ShaHandles
set_option autoImplicit false

theorem mutable_projection_with_caller {A : Type}
    (backend : PV_RDB2E_Dispatch.Backend)
    (shani : State → List U8 → Result State) (f : Frame)
    (valid : (position f).val<64) (caller : PV_RDB2D_SHAState.Restored → Result A) :
    (do let after ← finalize
          (PV_RDB2E_Dispatch.select backend PV_RDB2E_ConcreteSoft.software shani) f valid
        caller (forget after))=
      (PV_RDB2D_SHAState.completeState
        (PV_RDB2E_Dispatch.select backend PV_RDB2E_ConcreteSoft.software shani)
        f.core f.buffer (position f) >>= caller) := by
  have h := congrArg (fun r => r >>= caller)
    (PV_RDB2E_ConcreteSoft.both_backends backend shani f valid)
  simpa only [bind_assoc_eq,bind_tc_ok] using h

theorem fixed_carrier_dimensions (f : Frame) :
    f.core.state.val.length=8 ∧ f.buffer.val.length=64 ∧ f.output.val.length=32 :=
  ⟨f.core.state.property,f.buffer.property,f.output.property⟩

theorem fixed_block_size_u64 : (64#u64).val=64 := rfl

#print axioms fixed_carrier_dimensions
#print axioms fixed_block_size_u64

#print axioms mutable_projection_with_caller
end R1Z.PV_RDB2E_IndependentRoot
