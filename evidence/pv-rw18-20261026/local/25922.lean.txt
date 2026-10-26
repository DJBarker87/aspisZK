import R1Z.ProverRw18FieldStep
import R1Z.ProverRw18FieldModel
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18FieldFold
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning

-- Arbitrary slice elements are admitted. The actual scalar reducer supplies
-- their canonical products before addition. Only the initial two registers
-- and lambda need the stated canonicality for the field-value theorem.
theorem fold (values : List U32) (lambda out power : Raw)
    (hlambda : Canonical lambda) (hout : Canonical out) (hpower : Canonical power) :
    ∃ finalOut finalPower : Raw,
      PV_RW_CompressClosedFold.owned values (full lambda) (full out,full power)=
        ok (full finalOut,full finalPower) ∧
      Canonical finalOut ∧ Canonical finalPower ∧
      (decode finalOut,decode finalPower)=
        ProverRw18FieldModel.run values (decode lambda) (decode out,decode power) := by
  induction values generalizing out power with
  | nil => exact ⟨out,power,rfl,hout,hpower,rfl⟩
  | cons value values ih =>
    obtain ⟨out1,power1,hs,hco,hcp,hdo,hdp⟩ :=
      ProverRw18FieldStep.step out power lambda value hout hpower hlambda
    obtain ⟨finalOut,finalPower,hr,hcf,hcpow,hd⟩ := ih out1 power1 hco hcp
    refine ⟨finalOut,finalPower,?_,hcf,hcpow,?_⟩
    · change (do
        let next ← PV_RW_CompressConcrete.owned (full out) (full power) value (full lambda)
        PV_RW_CompressClosedFold.owned values (full lambda) next)=_
      rw [hs]
      simpa only [bind_tc_ok] using hr
    · simpa only [ProverRw18FieldModel.run,hdo,hdp] using hd

#print axioms fold
end R1Z.ProverRw18FieldFold
