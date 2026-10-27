import R1Z.PV_CB_ProducerLocalTuple
import R1Z.PV_CB_ProducerContext
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_ProducerLocalSelected
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_ProducerLimb
variable [ExternalTypes]

theorem tuple (ops : ExternalFuns) (trace : Trace) (input : PV_CB_ProducerTuple.Tuple)
    (vt : PV_CB_CanonicalArrays.Valid (PV_CB_ProducerLocalLimb.Reads trace) input.limbs)
    (vo : PV_CB_CanonicalArrays.Valid OffsetValid input.limbs) :
    PV_CB_ProducerPost.Good (PV_CB_CanonicalArrays.Valid PV_CB_CanonicalM31.Valid)
      (@host_semantic.copy_tuple_values _ (PV_CurrentScaleInstall.selected ops) trace input) := by
  rw [PV_CB_ProducerContext.tuple_congr (PV_CurrentScaleInstall.selected ops)
    (ProverRwDictionaryScalar.selected ops) (by rfl) (by rfl)]
  exact PV_CB_ProducerLocalTuple.tuple ops trace input vt vo
#print axioms tuple
end R1Z.PV_CB_ProducerLocalSelected
