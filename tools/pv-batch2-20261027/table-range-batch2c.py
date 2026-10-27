from pathlib import Path
import sys
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');p=L/'PV_B2_C_TableRange.lean'
s='import R1Z.PV_B2_C_Table\nset_option autoImplicit false\nnamespace PV_B2_C_TableRange\nopen Aeneas Aeneas.Std PV_B2_C_Table\n'
for i in range(32):
 s+=f'theorem chunk{i}_range : chunk{i}.all (fun x => decide (x.val < 1024)) = true := by decide\n#print axioms chunk{i}_range\n'
s+='''
/-- A symbolic composition over named 32-entry proofs, no large-type enumeration. -/
theorem values_range : values.all (fun x => decide (x.val < 1024)) = true := by
  simp only [values,List.all_append,'''+','.join(f'chunk{i}_range' for i in range(32))+''',Bool.and_self]

#print axioms values_range
end PV_B2_C_TableRange
'''
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
