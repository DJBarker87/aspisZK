from pathlib import Path
import re,sys,json
P=Path(__file__).resolve().parent;R=P.parents[1]
shapes=json.loads((P/'JGu_LEVEL_SHAPES.json').read_text())
for shape in shapes:
 ns=shape['module'];f=R/f'lean/{ns}.lean'
 if ns=='JGu_Level0_00':continue # Preserve the checked008 source, never rerun it.
 s=f.read_text();insert=[]
 if 'theorem read' in s:continue
 for row in shape['rows']:
  if row['pair']:continue
  w=row['w'];tag=f'{w:02}'
  a=s.index(f'  have read{tag} :');b=s.index(f'  have selected{tag}',a)
  block=s[a:b];head,body=block.split(' := by\n',1)
  head=head.replace('  have ', 'theorem ',1).replace(f'(s{tag} s).«at»',f"{32*row['before']}#usize")
  body=body.replace(f'    rw [cursor{tag}]\n','',1)
  body='\n'.join(line[2:] if line.startswith('  ') else line for line in body.rstrip().splitlines())+'\n'
  insert.append(head+' := by\n'+body+f'#print axioms read{tag}\n')
  # Exact header, with the current scratch cursor identified explicitly.
  replacement=block[:block.index(' := by\n')]+f' := by\n    rw [cursor{tag}]\n    exact read{tag}\n'
  s=s[:a]+replacement+s[b:]
 marker=' theorem source';idx=s.index(marker)
 s=s[:idx]+''.join(insert)+s[idx:]
 s=s.replace('set_option autoImplicit false\n','set_option autoImplicit false\nset_option linter.unusedSimpArgs false\n',1)
 if '--check' in sys.argv:pass
 else:f.write_text(s)
print('Split physical reads into per-cell named declarations; retained checked level0_00')
