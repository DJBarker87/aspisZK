"""Canonical table certificates, split at the cohort's existing 32-entry chunks.
No full-table numeral reduction and no heartbeat/depth override.
"""
from pathlib import Path
E=Path(__file__).resolve().parent
for table in 'AB':
 for i in range(16):
  name=f'NEA_Table{table}{i:02d}';chunk=f'AspisR1QueryGeometryActual.fast_domain.TABLE_{table}_chunk_{i:02d}'
  s=f'''import AspisR1QueryGeometryActual.Funs
set_option autoImplicit false
namespace {name}
open Aeneas Aeneas.Std

theorem canonical (p : U32 × U32) (member : p ∈ {chunk}) :
    p.1.val < 2147483647 ∧ p.2.val < 2147483647 := by
  simp only [{chunk}, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with '''+' | '.join(['rfl']*32)+'''
  all_goals constructor <;> decide

#print axioms canonical
end '''+name+'\n'
  (E/(name+'.lean')).write_text(s)
