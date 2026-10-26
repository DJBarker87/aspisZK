import R1Z.PDict_CopyClosure222
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_WorkTransport222
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Source-level extensional contract for existing open operation257.
This is not a native cost/trace law and is not asserted for arbitrary dictionaries. -/
def WorkExtensional (ops : ExternalFuns) : Prop :=
  ∀ {T A B : Type} (fa : core.ops.function.Fn A Usize T)
    (fb : core.ops.function.Fn B Usize T) (a : A) (b : B) (stage n : Usize),
    (∀ i, fa.call a i = fb.call b i) →
    @host_work.map _ ops T A fa stage n a = @host_work.map _ ops T B fb stage n b

theorem assignment (ops : ExternalFuns) {A B : Type}
    (oa : host_sumcheck.Oracle A) (ob : host_sumcheck.Oracle B) (a : A) (b : B)
    (h : ∀ p, oa.evaluate a p = ob.evaluate b p)
    (point : Array aspis_core.field.QM31 10#usize) (round assignments i : Usize) :
    @host_sumcheck.evaluate_assignment _ ops A oa a point round assignments i =
    @host_sumcheck.evaluate_assignment _ ops B ob b point round assignments i := by
  delta host_sumcheck.evaluate_assignment
  repeat first
    | exact h _
    | (apply PDict_FallibleTransport.bind_congr; intro x)

#print axioms assignment
end R1Z.PDict_WorkTransport222
