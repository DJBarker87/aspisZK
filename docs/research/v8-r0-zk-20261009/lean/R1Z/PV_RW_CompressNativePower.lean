import R1Z.PV_RW_CompressPowerFold
import R1Z.PV_RW_IteratorStateLoop
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_CompressNativePower
open Aeneas Aeneas.Std Result ProverRwDictionaryTower
abbrev Q := ProverRwFull.aspis_core.field.QM31
variable [ProverRwFull.ExternalTypes]

theorem final_power (ops : ProverRwFull.ExternalFuns) (values : Slice U32)
    (lambda out power : Q) :
    mapResult Prod.snd (PV_RW_IteratorStateLoop.run ops lambda
      (⟨values,0⟩ : PV_RW_IteratorStateLoop.Iter) (out,power))=
      PV_RW_CompressPowerFold.powerRun lambda values.val.length power := by
  rw [PV_RW_IteratorStateLoop.owned,← PV_RW_CompressClosedFold.owned_equal]
  exact PV_RW_CompressPowerFold.projection values.val lambda out power

theorem arity16 (ops : ProverRwFull.ExternalFuns) (values : Array U32 16#usize)
    (lambda out power : Q) :
    mapResult Prod.snd (PV_RW_IteratorStateLoop.run ops lambda
      (⟨Array.to_slice values,0⟩ : PV_RW_IteratorStateLoop.Iter) (out,power))=
      PV_RW_CompressPowerFold.powerRun lambda 16 power := by
  have shape : (Array.to_slice values).val.length=16 := values.property
  simpa only [shape] using final_power ops (Array.to_slice values) lambda out power
#print axioms final_power
#print axioms arity16
end R1Z.PV_RW_CompressNativePower
