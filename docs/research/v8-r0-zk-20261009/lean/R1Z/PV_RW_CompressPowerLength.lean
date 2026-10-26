import R1Z.PV_RW_CompressNativePower
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_CompressPowerLength
open Aeneas Aeneas.Std Result ProverRwDictionaryTower
abbrev Q := ProverRwFull.aspis_core.field.QM31
variable [ProverRwFull.ExternalTypes]

theorem equal_length (leftOps rightOps : ProverRwFull.ExternalFuns)
    (left right : Slice U32) (same : left.val.length=right.val.length)
    (lambda leftOut rightOut power : Q) :
    mapResult Prod.snd (PV_RW_IteratorStateLoop.run leftOps lambda
      (⟨left,0⟩ : PV_RW_IteratorStateLoop.Iter) (leftOut,power))=
      mapResult Prod.snd (PV_RW_IteratorStateLoop.run rightOps lambda
      (⟨right,0⟩ : PV_RW_IteratorStateLoop.Iter) (rightOut,power)) := by
  rw [PV_RW_CompressNativePower.final_power,PV_RW_CompressNativePower.final_power,same]

-- Applies to every pair of actual arity16 raw-input arrays and accumulators.
theorem arity16 (leftOps rightOps : ProverRwFull.ExternalFuns)
    (left right : Array U32 16#usize) (lambda leftOut rightOut power : Q) :
    mapResult Prod.snd (PV_RW_IteratorStateLoop.run leftOps lambda
      (⟨Array.to_slice left,0⟩ : PV_RW_IteratorStateLoop.Iter) (leftOut,power))=
      mapResult Prod.snd (PV_RW_IteratorStateLoop.run rightOps lambda
      (⟨Array.to_slice right,0⟩ : PV_RW_IteratorStateLoop.Iter) (rightOut,power)) := by
  rw [PV_RW_CompressNativePower.arity16,PV_RW_CompressNativePower.arity16]
#print axioms equal_length
#print axioms arity16
end R1Z.PV_RW_CompressPowerLength
