import R1Z.ProverRw18FieldPowerPure
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18FinalPower16
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning

theorem exact_power (values : Array U32 16#usize) (lambda : Raw) (out : Q)
    (hlambda : Canonical lambda) :
    ProverRwDictionaryTower.mapResult Prod.snd
      (PV_RW_CompressClosedFold.owned values.val (full lambda) (out,full lambda))=
        ok (full (ProverRw18FieldEncode.encode ((decode lambda)^17))) := by
  rw [ProverRw18FieldPowerPure.projection _ lambda lambda out hlambda hlambda]
  have length : values.val.length=16 := values.property
  rw [length,← pow_succ']

variable [ProverRwFull.ExternalTypes]
theorem combined (ops : ProverRwFull.ExternalFuns) (values : Array U32 16#usize)
    (lambda : Raw) (out : Q) (hlambda : Canonical lambda) :
    ProverRwDictionaryTower.mapResult Prod.snd
      (PV_RW_IteratorStateLoop.run ops (full lambda)
        (⟨Array.to_slice values,0⟩ : core.slice.iter.Iter U32) (out,full lambda))=
          ok (full (ProverRw18FieldEncode.encode ((decode lambda)^17))) := by
  rw [PV_RW_IteratorStateLoop.owned]
  exact exact_power values lambda out hlambda

#print axioms exact_power
#print axioms combined
end R1Z.ProverRw18FinalPower16
