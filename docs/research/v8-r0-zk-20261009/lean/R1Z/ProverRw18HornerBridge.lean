import R1Z.ProverRw18GenericPolynomial
import R1Z.ProverRw18FieldModel
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18HornerBridge
open Aeneas Aeneas.Std ProverRw18FieldMeaning

theorem eval (values : List U32) (lambda : K) :
    ProverRw18FieldModel.eval values lambda=
      ProverRw18GenericPolynomial.horner (values.map (fun value => (value.val : K))) lambda := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    rw [ProverRw18FieldModel.eval,List.map_cons,ProverRw18GenericPolynomial.horner,ih]

#print axioms eval
end R1Z.ProverRw18HornerBridge
