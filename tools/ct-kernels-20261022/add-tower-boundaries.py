#!/usr/bin/env python3
"""One-shot source migration retained to document the smaller proof boundary."""
from pathlib import Path
import re
p=Path(__file__).with_name('lib.rs');s=p.read_text();start=s.index('#[cfg(kani)] mod parametric {');end=s.index('#[cfg(kani)] mod closure',start);part=s[start:end]
assert 'fn c_cm_mul' not in part
helpers=''
for pre,module in [('c','field'),('r','reference')]:
 for op,id,n in [('mul',10,2),('square',12,1),('mul_m31',14,2)]:
  typ=module+'::CM31';rhs=(f',b:{typ}' if op=='mul' else f',b:{module}::M31' if op=='mul_m31' else '')
  bb=['b.a.0','b.b.0'] if op=='mul' else ['b.0','b.0'] if op=='mul_m31' else ['0','0']
  helpers+=f'fn {pre}_cm_{op}(a:{typ}{rhs})->{typ} {{{typ} {{a:{module}::M31(leaf({id},a.a.0 as u64,{bb[0]} as u64)),b:{module}::M31(leaf({id+1},a.b.0 as u64,{bb[1]} as u64))}}}}\n'
 for op,id in [('mul',20),('square',24),('mul_m31',28)]:
  typ=module+'::QM31';rhs=(f',b:{typ}' if op=='mul' else f',b:{module}::M31' if op=='mul_m31' else '')
  helpers+=f'fn {pre}_qm_{op}(a:{typ}{rhs})->{typ} {{'
  vals=[]
  for i,path in enumerate(['c0.a','c0.b','c1.a','c1.b']):
   bb=f'b.{path}.0' if op=='mul' else 'b.0' if op=='mul_m31' else '0'
   vals.append(f'{module}::M31(leaf({id+i},a.{path}.0 as u64,{bb} as u64))')
  helpers+=typ+'{c0:'+module+'::CM31{a:'+vals[0]+',b:'+vals[1]+'},c1:'+module+'::CM31{a:'+vals[2]+',b:'+vals[3]+'}}}\n'
i=part.index('#[kani::proof]');part=part[:i]+helpers+part[i:]
for m in list(re.finditer(r'fn (qm|wide)_([a-z0-9_]+)\(\)',part))[::-1]:
 pos=m.start();level=m.group(1);attrs=''
 for pre,module in [('c','field'),('r','reference')]:
  for op in ['mul','square','mul_m31']:
   attrs+=f'#[kani::stub({module}::CM31::{op}, {pre}_cm_{op})]\n'
   if level=='wide':attrs+=f'#[kani::stub({module}::QM31::{op}, {pre}_qm_{op})]\n'
 part=part[:pos]+attrs+part[pos:]
p.write_text(s[:start]+part+s[end:])
