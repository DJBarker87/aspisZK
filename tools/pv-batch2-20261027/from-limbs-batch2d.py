"""Eight symbolic limb reads; never reduce multiplication results in the kernel."""
from pathlib import Path
import sys
s='''import R1Z.PV_B2_D_QuarticCanonical
set_option autoImplicit false
namespace PV_B2_D_FromLimbs
open Aeneas Aeneas.Std Result PV_B2_251c1 PV_B2_D_QuarticCanonical
abbrev Q := aspis_core.field.QM31
abbrev E := aspis_core.field.wide_exact.WideExact
def limbs (a b : Q) : Array U32 8#usize :=
  Array.make 8#usize [a.c0.a,a.c0.b,a.c1.a,a.c1.b,b.c0.a,b.c0.b,b.c1.a,b.c1.b]
'''
fields=[f'{q}.{c}.{v}' for q in ['a','b'] for c in ['c0','c1'] for v in ['a','b']]
for i,f in enumerate(fields):
 s+=f'''theorem read{i} (a b : Q) : Array.index_usize (limbs a b) {i}#usize = ok {f} := by rfl
#print axioms read{i}
'''
s+='''theorem source (a b : Q) (ha : QC a) (hb : QC b) :
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
  simp only ['''+','.join(f'read{i}' for i in range(8))+',bind_tc_ok,'+','.join(f'n{i}' for i in range(8))+''',if_neg,if_false]

#print axioms source
end PV_B2_D_FromLimbs
'''
p=Path('docs/research/v8-r0-zk-20261009/lean/R1Z/PV_B2_D_FromLimbs.lean')
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
