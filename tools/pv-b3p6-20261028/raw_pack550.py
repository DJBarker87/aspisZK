"""Generate four SMALL wrapping pack laws, parsed from the frozen SSA suffix.
Each output is independent; arithmetic stays irreducible. No whole raw reduction.
"""
from pathlib import Path
import re,json,hashlib
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';R=D/'resume18'
p=L/'PV_B3P_P227_03d.lean';s=p.read_text();lines=s[s.index('  let i81 ←'):s.index('  ok (Array.make 4#usize [ i95')].splitlines()
ends=['i95','i109','i118','i125'];chunks=[];chunk=[]
for line in lines:
 chunk.append(line)
 if any(line.startswith('  let '+name+' ←')for name in ends):
  chunks.append(chunk);chunk=[]
assert len(chunks)==4 and not chunk
rename={'a24':'a','a25':'b','a26':'c','a27':'d','i80':'bound'}
# Independently parse the four shipped Rust expressions. Comparison retains
# every operator, associativity edge and row/limb index, including subtraction.
dep=Path('crates/aspis-statement/src/state_only_poseidon.rs')
deps=dep.read_text().split('fn external_local_packed_raw',1)[1]
pack=deps.split('let packed = [',1)[1].split('];',1)[0]
expressions=[x.strip()for x in pack.split(',')if x.strip()]
assert len(expressions)==4

def parse(expr):
 ts=re.findall(r'local\[\d\]\[\d\]|bound|\d+|[()+*\-]',expr);pos=0
 assert ''.join(ts)==re.sub(r'\s+','',expr)
 def term(minimum=0):
  nonlocal pos
  t=ts[pos];pos+=1
  if t=='(':
   node=term();assert ts[pos]==')';pos+=1
  elif t.startswith('local'):
   row,limb=re.findall(r'\d',t);node=('limb','abcd'[int(row)],limb)
  else:node=('const',t)
  while pos<len(ts)and ts[pos]in ['+','-','*']and (20 if ts[pos]=='*'else 10)>=minimum:
   op=ts[pos];pos+=1;right=term((20 if op=='*'else 10)+1)
   node=({'+':'add','-':'sub','*':'mul'}[op],node,right)
  return node
 node=term();assert pos==len(ts);return node
source_trees=[parse(e)for e in expressions]
notes=[]
for j,ls in enumerate(chunks):
 raw='\n'.join(ls)
 for a,b in rename.items():raw=re.sub(r'\b'+a+r'\b',b,raw)
 env={};trees={};reads=[]
 for line in raw.splitlines():
  m=re.fullmatch(r'  let (\w+) ← Array.index_usize ([abcd]) (\d)#usize',line)
  if m:
   var,row,i=m.groups();env[var]=f'(limb_at550 {row} {i}#usize (by decide))';trees[var]=('limb',row,i);reads.append((row,i));continue
  m=re.fullmatch(r'  let (\w+) ← lift \(Std.U64.wrapping_(add|sub|mul) (\w+(?:#u64)?) (\w+(?:#u64)?)\)',line);assert m,line
  v,op,left,right=m.groups();trees[v]=(op,trees.get(left,('const',left.removesuffix('#u64'))),trees.get(right,('const',right.removesuffix('#u64'))));env[v]='(U64.wrapping_'+op+' '+env.get(left,left)+' '+env.get(right,right)+')'
 out=ends[j];assert trees[out]==source_trees[j],(j,trees[out],source_trees[j]);name=f'raw_pack{j}_550';mod=f'PV_B3P_RawPack{j}550227'
 text='''import PV_B3P_RawRows550227
namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
'''
 if j==0:
  text+='''\ndef limb_at550 (row : Limbs64_550) (i : Usize) (bound : i.val < 4) : U64 :=
  row.val[i.val]'(by rw [row.property]; exact bound)
'''
 else:text=text.replace('import PV_B3P_RawRows550227',f'import PV_B3P_RawPack{j-1}550227')
 text+=f'\ndef {name} (a b c d : Limbs64_550) (bound : U64) : Result U64 := do\n'+raw+f'\n  .ok {out}\n'
 text+='\nattribute [local irreducible] U64.wrapping_add U64.wrapping_sub U64.wrapping_mul\n'
 text+=f'\ntheorem raw_pack{j}_value550 (a b c d : Limbs64_550) (bound : U64) :\n    {name} a b c d bound =\n      .ok {env[out]} := by\n  unfold {name}\n  simp only [lift, bind_tc_ok]\n'
 for row,i in reads:
  text+=f'  rw [PV_B3P_SelectIndex227.index_value {row} {i}#usize (by decide)]\n  simp only [bind_tc_ok]\n'
 text+='  rfl\n'+f'\n#print axioms raw_pack{j}_value550\nend PV_B3P_Association550227\n'
 (L/(mod+'.lean')).write_text(text)
 notes.append(dict(module=mod,ssa_output=out,indexed_reads=len(reads),source_suffix_sha256=hashlib.sha256(raw.encode()).hexdigest()))
(R/'RAW-PACK-GENERATOR-D550.json').write_text(json.dumps(dict(emission=str(p),emission_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),outputs=notes,deployed_source=str(dep),deployed_source_sha256=hashlib.sha256(dep.read_bytes()).hexdigest(),source_expressions=expressions,all_operator_trees_identical=True,status='isolated output laws with independently checked shipped expression trees; full raw Link remains open'),indent=2)+'\n')
print(json.dumps(dict(outputs=4,indexed_reads=sum(x['indexed_reads']for x in notes))))
