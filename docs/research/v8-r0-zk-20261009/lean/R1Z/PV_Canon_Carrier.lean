import R1Z.ProverRwP7CurrentFieldSource
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std ProverRwFull
/-- Predicates on the actual extracted carriers, not residues modulo P. -/
def M (x : aspis_core.field.M31) : Prop := x.val < 2147483647
def C (x : aspis_core.field.CM31) : Prop := M x.a ∧ M x.b
def Q (x : aspis_core.field.QM31) : Prop := C x.c0 ∧ C x.c1
def Coeffs (xs : Array aspis_core.field.QM31 28#usize) : Prop :=
  ∀ x ∈ xs.val, Q x
 theorem zero : M (0#u32) := by change 0 < 2147483647; omega
 theorem one : M (1#u32) := by change 1 < 2147483647; omega
 theorem constructor (x : U32) (hx : x.val < 2147483647) : M x := hx
 theorem cm31_constructor (a b : U32) (ha : M a) (hb : M b) : C ⟨a,b⟩ := ⟨ha,hb⟩
 theorem qm31_constructor (a b : aspis_core.field.CM31) (ha : C a) (hb : C b) :
    Q ⟨a,b⟩ := ⟨ha,hb⟩
#print axioms zero
#print axioms one
#print axioms constructor
#print axioms cm31_constructor
#print axioms qm31_constructor
end R1Z.PV_Canon
