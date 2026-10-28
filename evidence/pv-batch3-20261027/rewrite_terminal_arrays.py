"""Eliminate noncapturing array closures in gated terminal copies, preserving order."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2]
macro='''\n// Closure-free array construction, evaluated in increasing source index order.\nmacro_rules! qm31_array {\n    ($n:expr, $index:ident, $body:expr) => {{\n        let mut output = [QM31::ZERO; $n];\n        let mut $index = 0usize;\n        while $index < $n {\n            output[$index] = $body;\n            $index += 1;\n        }\n        output\n    }};\n}\n'''
for name,lengths in [('host_terminal.rs',[4,4,16,16,16,4,16,16,16,'STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS']),('host_copy_terminal.rs',[4,4,4])]:
 p=root/'crates/aspis-r1-cost-probe/src'/name;s=p.read_text();offset=0
 for n in lengths:
  m=re.search(r'core::array::from_fn\(\|(\w+)\|',s[offset:]);assert m,name
  a=offset+m.start();expr=offset+m.end();depth=1;i=expr
  while depth:
   if s[i]=='(':depth+=1
   if s[i]==')':depth-=1
   i+=1
  body=s[expr:i-1].strip();replacement=f'qm31_array!({n}, {m[1]}, {body})'
  s=s[:a]+replacement+s[i:];offset=a+len(replacement)
 # Macro must precede uses, after module docs.
 pos=s.index('use ');s=s[:pos]+macro+'\n'+s[pos:]
 if name=='host_terminal.rs':
  a=s.index('    view[..9]');b=s.index('\n}',a)
  s=s[:a]+'''    let mut acc = view[9];
    let mut index = 9usize;
    while index > 0 {
        index -= 1;
        acc = acc.add(acc).add(view[index]);
    }
    acc'''+s[b:]
  a=s.index('    let factor = |a: QM31, b: QM31| {');b=s.index('    let mut product',a)
  s=s[:a]+s[b:];s=s.replace('factor(left[','equality_factor(left[')
  s+='''\n#[inline(always)]\nfn equality_factor(a: QM31, b: QM31) -> QM31 {\n    let ab = a.mul(b);\n    QM31::ONE.sub(a).sub(b).add(ab).add(ab)\n}\n'''
 p.write_text(s)
