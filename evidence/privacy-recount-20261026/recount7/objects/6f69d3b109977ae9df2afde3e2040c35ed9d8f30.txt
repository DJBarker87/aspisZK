import PV_B3_FieldTransport
namespace PV_B3_Canonical
open Aeneas Aeneas.Std Result PV_B3_FieldTransport
set_option autoImplicit false
-- These predicates are native limb bounds, with no residue quotient coercion.
def M (x : U32) : Prop := x.val < 2147483647
def C (x : New.C) : Prop := M x.a ∧ M x.b
def Q (x : New.Q) : Prop := C x.c0 ∧ C x.c1
theorem zero : M 0#u32 := by change 0<2147483647; omega
theorem one : M 1#u32 := by change 1<2147483647; omega
theorem c_mk (a b : U32) (ha : M a) (hb : M b) : C ⟨a,b⟩ := ⟨ha,hb⟩
theorem q_mk (a b : New.C) (ha : C a) (hb : C b) : Q ⟨a,b⟩ := ⟨ha,hb⟩
#print axioms zero
#print axioms one
#print axioms c_mk
#print axioms q_mk
end PV_B3_Canonical
