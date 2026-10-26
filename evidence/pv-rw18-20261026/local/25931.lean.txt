import R1Z.ProverRw18FieldFold
import R1Z.ProverRw18FieldEncode
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18FieldStateReference
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning

def reference (values : List U32) (lambda out power : Raw) : Result (Q × Q) :=
  let state := ProverRw18FieldModel.run values (decode lambda) (decode out,decode power)
  ok (full (ProverRw18FieldEncode.encode state.1),full (ProverRw18FieldEncode.encode state.2))

theorem owned (values : List U32) (lambda out power : Raw)
    (hlambda : Canonical lambda) (hout : Canonical out) (hpower : Canonical power) :
    PV_RW_CompressClosedFold.owned values (full lambda) (full out,full power)=
      reference values lambda out power := by
  obtain ⟨finalOut,finalPower,hr,hco,hcp,hd⟩ :=
    ProverRw18FieldFold.fold values lambda out power hlambda hout hpower
  have outValue := congrArg Prod.fst hd
  have powerValue := congrArg Prod.snd hd
  have outSame : finalOut=ProverRw18FieldEncode.encode
      (ProverRw18FieldModel.run values (decode lambda) (decode out,decode power)).1 := by
    apply ProverRw18FieldInjective.raw _ _ hco (ProverRw18FieldEncode.canonical _)
    rw [ProverRw18FieldEncode.decoded]
    exact outValue
  have powerSame : finalPower=ProverRw18FieldEncode.encode
      (ProverRw18FieldModel.run values (decode lambda) (decode out,decode power)).2 := by
    apply ProverRw18FieldInjective.raw _ _ hcp (ProverRw18FieldEncode.canonical _)
    rw [ProverRw18FieldEncode.decoded]
    exact powerValue
  rw [hr,outSame,powerSame]
  rfl

variable [ProverRwFull.ExternalTypes]

theorem combined (ops : ProverRwFull.ExternalFuns) (values : Slice U32) (lambda out power : Raw)
    (hlambda : Canonical lambda) (hout : Canonical out) (hpower : Canonical power) :
    PV_RW_IteratorStateLoop.run ops (full lambda) (⟨values,0⟩ : core.slice.iter.Iter U32)
      (full out,full power)=reference values.val lambda out power := by
  rw [PV_RW_IteratorStateLoop.owned]
  exact owned values.val lambda out power hlambda hout hpower

#print axioms owned
#print axioms combined
end R1Z.ProverRw18FieldStateReference
