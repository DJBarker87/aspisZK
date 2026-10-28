from pathlib import Path
p=['import NBA_ArrayEight','set_option autoImplicit false','namespace AspisR1.NBA_Store8','open Aeneas Aeneas.Std Result','variable {α : Type}']
args='(z x0 x1 x2 x3 x4 x5 x6 x7 : α)'
vals='z x0 x1 x2 x3 x4 x5 x6 x7'
for n in range(9):
 ls=[f'x{i}' if i<n else 'z' for i in range(8)]
 p += [f'def s{n} {args} : Array α 8#usize := Array.make 8#usize [{",".join(ls)}]']
p += [f'def back {args} (x : α) : Array α 8#usize := Array.make 8#usize [x,z,z,z,z,z,z,z]',f'theorem mutable {args} : Array.index_mut_usize (s0 {vals}) 0#usize=ok (z,back {vals}) := by rfl',f'theorem write0 {args} : back {vals} x0=s1 {vals} := rfl']
for i in range(1,8):p += [f'theorem write{i} {args} : Array.update (s{i} {vals}) {i}#usize x{i}=ok (s{i+1} {vals}) := by rfl']
for i in range(8):p += [f'theorem read{i} {args} : Array.index_usize (s{i+1} {vals}) {i}#usize=ok x{i} := by rfl']
for n in ['mutable']+[f'write{i}' for i in range(8)]+[f'read{i}' for i in range(8)]:p += [f'#print axioms {n}']
p+=['end AspisR1.NBA_Store8']
Path('lean/NBA_Store8.lean').write_text('\n'.join(p)+'\n')
