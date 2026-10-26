import R1Z.ProverRw18FieldPower
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18FieldPowerPure
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning

-- This equality is pure and does not need the unused ExternalTypes section
-- parameter carried by the older owned_equal lemma.
theorem fold_equal (values : List U32) (lambda : Q) (state : Q × Q) :
    PV_RW_CompressClosedFold.fold values lambda state=
      PV_RW_CompressClosedFold.owned values lambda state := by
  have steps : (fun (value : U32) (state : Q × Q) =>
      PV_RW_CompressConcrete.step state.1 state.2 value lambda)=
      (fun value state => PV_RW_CompressConcrete.owned state.1 state.2 value lambda) := by
    funext value state
    exact PV_RW_CompressConcrete.current_owned state.1 state.2 value lambda
  unfold PV_RW_CompressClosedFold.fold PV_RW_CompressClosedFold.owned
  rw [steps]

theorem projection (values : List U32) (lambda power : Raw) (out : Q)
    (hlambda : Canonical lambda) (hpower : Canonical power) :
    ProverRwDictionaryTower.mapResult Prod.snd
      (PV_RW_CompressClosedFold.owned values (full lambda) (out,full power))=
        ok (full (ProverRw18FieldEncode.encode (decode power*(decode lambda)^values.length))) := by
  rw [← fold_equal,PV_RW_CompressPowerFold.projection]
  obtain ⟨final,hr,hc,hd⟩ := ProverRw18FieldPower.run values.length lambda power hlambda hpower
  have same : final=ProverRw18FieldEncode.encode (decode power*(decode lambda)^values.length) := by
    apply ProverRw18FieldInjective.raw _ _ hc (ProverRw18FieldEncode.canonical _)
    rw [ProverRw18FieldEncode.decoded]
    exact hd
  rw [hr,same]

#print axioms fold_equal
#print axioms projection
end R1Z.ProverRw18FieldPowerPure
