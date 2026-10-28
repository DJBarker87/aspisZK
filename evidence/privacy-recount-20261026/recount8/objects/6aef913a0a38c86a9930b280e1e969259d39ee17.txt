import R1Z.PV_RDB2C_PV_B2_D_QuarticCanonical
set_option autoImplicit false
namespace PV_B2_D_FromLimbs
open Aeneas Aeneas.Std Result PV_B2_251c1 PV_B2_D_QuarticCanonical
abbrev Q := aspis_core.field.QM31
abbrev E := aspis_core.field.wide_exact.WideExact
def limbs (a b : Q) : Array U32 8#usize :=
  Array.make 8#usize [a.c0.a,a.c0.b,a.c1.a,a.c1.b,b.c0.a,b.c0.b,b.c1.a,b.c1.b]
theorem read0 (a b : Q) : Array.index_usize (limbs a b) 0#usize = ok a.c0.a := by rfl
#print axioms read0
theorem read1 (a b : Q) : Array.index_usize (limbs a b) 1#usize = ok a.c0.b := by rfl
#print axioms read1
theorem read2 (a b : Q) : Array.index_usize (limbs a b) 2#usize = ok a.c1.a := by rfl
#print axioms read2
theorem read3 (a b : Q) : Array.index_usize (limbs a b) 3#usize = ok a.c1.b := by rfl
#print axioms read3
theorem read4 (a b : Q) : Array.index_usize (limbs a b) 4#usize = ok b.c0.a := by rfl
#print axioms read4
theorem read5 (a b : Q) : Array.index_usize (limbs a b) 5#usize = ok b.c0.b := by rfl
#print axioms read5
theorem read6 (a b : Q) : Array.index_usize (limbs a b) 6#usize = ok b.c1.a := by rfl
#print axioms read6
theorem read7 (a b : Q) : Array.index_usize (limbs a b) 7#usize = ok b.c1.b := by rfl
#print axioms read7
theorem source (a b : Q) (ha : QC a) (hb : QC b) :
  aspis_core.field.wide_exact.WideExact.from_limbs (limbs a b) = ok (some (⟨a,b⟩ : E)) := by
  have n0 : ¬ a.c0.a ≥ aspis_core.field.P := by
    rw [PV_B2_C_251FieldTotal.P]
    exact Nat.not_le.mpr ha.1.1
  have n1 : ¬ a.c0.b ≥ aspis_core.field.P := by
    rw [PV_B2_C_251FieldTotal.P]
    exact Nat.not_le.mpr ha.1.2
  have n2 : ¬ a.c1.a ≥ aspis_core.field.P := by
    rw [PV_B2_C_251FieldTotal.P]
    exact Nat.not_le.mpr ha.2.1
  have n3 : ¬ a.c1.b ≥ aspis_core.field.P := by
    rw [PV_B2_C_251FieldTotal.P]
    exact Nat.not_le.mpr ha.2.2
  have n4 : ¬ b.c0.a ≥ aspis_core.field.P := by
    rw [PV_B2_C_251FieldTotal.P]
    exact Nat.not_le.mpr hb.1.1
  have n5 : ¬ b.c0.b ≥ aspis_core.field.P := by
    rw [PV_B2_C_251FieldTotal.P]
    exact Nat.not_le.mpr hb.1.2
  have n6 : ¬ b.c1.a ≥ aspis_core.field.P := by
    rw [PV_B2_C_251FieldTotal.P]
    exact Nat.not_le.mpr hb.2.1
  have n7 : ¬ b.c1.b ≥ aspis_core.field.P := by
    rw [PV_B2_C_251FieldTotal.P]
    exact Nat.not_le.mpr hb.2.2
  unfold aspis_core.field.wide_exact.WideExact.from_limbs
  simp only [read0,read1,read2,read3,read4,read5,read6,read7,bind_tc_ok,n0,n1,n2,n3,n4,n5,n6,n7,if_neg,if_false]

#print axioms source
end PV_B2_D_FromLimbs
