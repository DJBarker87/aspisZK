import R1Z.ProverRw18GenericPolynomial
import R1Z.ProverRw18FieldMeaning
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18CopySpecialized
open ProverRw18FieldMeaning

theorem copy (tag : K) (values : Fin 16 → K) (lambda : K) :
    tag+lambda*ProverRw18GenericPolynomial.horner (List.ofFn values) lambda=
      (R0P.compressPoly (tag,values)).eval lambda :=
  ProverRw18GenericPolynomial.copy tag values lambda

#print axioms copy
end R1Z.ProverRw18CopySpecialized
