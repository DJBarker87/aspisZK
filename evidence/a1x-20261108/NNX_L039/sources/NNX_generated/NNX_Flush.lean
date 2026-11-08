import NNX_QueryOutput
import NNV_CurrentFlush
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_Flush
open Aeneas Aeneas.Std Result NNH_Run5bCtx
/-- The flush input-domain comes from the SAME returned query loop, rather
than an independent native success or a new callee-domain premise. -/
theorem source {W Tx : Type} (c : Ctx W Tx) (input : LIBC_QueryLoop.Args)
 (domain : LIBC_QueryLoop.Domain input) (after : LIB_VCarriers.Acc)
 (pending : LIB_VCarriers.Weights)
 (called : LIBC_QueryLoop.value input (envOf c) = .ok (after,pending)) :
 (DrvC_Installation.currentInstalled (configuration c)).op17 (Tx1Q_Carriers.unPending pending)
  (Tx1Q_Carriers.unAccumulator (LIBC_VStateCarriers.toAcc after)).weights.deref =
 .ok (Tx1Q_Carriers.slice Tx1Q_Carriers.unK (NJJ_Flush.output pending)) :=
 NNV_CurrentFlush.returned c (pending,after) (NNX_QueryOutput.domain input (envOf c) domain after pending called)
#print axioms source
end AspisR1.NNX_Flush
end
