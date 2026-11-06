import NJB_CopyResidual
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJB_StubLaws
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
/-- Paired full-Result laws: each native log is universal in canonical reply;
the root instantiates that reply with this emitted operation's actual value. -/
theorem qm_mul (x y : NQ) (hx : Canon x) (hy : Canon y) :
 ∃ z, field.QM31.mul x y=ok z ∧ Canon z ∧ decode z=decode x*decode y :=
 JFy_FieldTotal.mul x y hx hy
theorem qm_add (x y : NQ) (hx : Canon x) (hy : Canon y) :
 ∃ z, field.QM31.add x y=ok z ∧ Canon z ∧ decode z=decode x+decode y :=
 FIv_PreparedTotal.add x y hx hy
theorem qm_sub (x y : NQ) (hx : Canon x) (hy : Canon y) :
 ∃ z, field.QM31.sub x y=ok z ∧ Canon z ∧ decode z=decode x-decode y :=
 JFy_FieldTotal.sub x y hx hy
#print qm_mul
#print qm_add
#print qm_sub
#print axioms qm_mul
#print axioms qm_add
#print axioms qm_sub
end AspisR1.NJB_StubLaws
end
