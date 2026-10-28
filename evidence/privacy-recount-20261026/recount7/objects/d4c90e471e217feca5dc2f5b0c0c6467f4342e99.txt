import R1Z.ProverRwFullFuns
set_option autoImplicit false
namespace R1Z.PV_Join_Canonical5
open Aeneas Aeneas.Std ProverRwFull
abbrev P : Nat := 2147483647
def M (x : aspis_core.field.M31) : Prop := x.val < P
def C (x : aspis_core.field.CM31) : Prop := M x.a ∧ M x.b
def Q (x : aspis_core.field.QM31) : Prop := C x.c0 ∧ C x.c1
def QArray {n : Usize} (xs : Array aspis_core.field.QM31 n) : Prop :=
  ∀ x ∈ xs.val, Q x

theorem m_zero : M (0#u32) := by change 0 < 2147483647; omega
theorem m_one : M (1#u32) := by change 1 < 2147483647; omega
theorem c_mk (a b : aspis_core.field.M31) (ha : M a) (hb : M b) : C ⟨a,b⟩ := ⟨ha,hb⟩
theorem q_mk (a b : aspis_core.field.CM31) (ha : C a) (hb : C b) : Q ⟨a,b⟩ := ⟨ha,hb⟩
theorem q_zero : Q ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩ := ⟨⟨m_zero,m_zero⟩,⟨m_zero,m_zero⟩⟩
theorem q_one : Q ⟨⟨1#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩ := ⟨⟨m_one,m_zero⟩,⟨m_zero,m_zero⟩⟩
#print axioms m_zero
#print axioms m_one
#print axioms c_mk
#print axioms q_mk
#print axioms q_zero
#print axioms q_one
end R1Z.PV_Join_Canonical5
