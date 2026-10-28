"""Focused inputs to unchanged reservation and host runner; no new copy stub."""
from KNA_driver import *
PREV=E.parent/'kani-reverify2-20261028'
BASE='''#![feature(allocator_api)]
extern crate alloc;
mod KMX_stubs;
#[path="KMY_field.rs"] mod field;
use field::{QM31 as K,CM31,M31};
'''
ATTR='''#[kani::proof] #[kani::unwind(1769)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
'''
def query(cap,lo,hi):
 return f'''let initial:[u8;{cap}]=kani::any();let source:[u8;4]=kani::any();
let i:usize=kani::any();kani::assume({lo}<=i && i<{hi});let len=64+4*i;
let mut out=alloc::vec::Vec::from(initial);out.truncate(len);
assert_eq!(out.len(),len);assert_eq!(out.capacity(),{cap});
let p:usize=kani::any();kani::assume(p<len);assert_eq!(out[p],initial[p]);
KMX_stubs::KMX_extend_from_slice(&mut out,&source);
assert_eq!(out.len(),len+4);assert_eq!(out.capacity(),{cap});
let j:usize=kani::any();kani::assume(j<len+4);
assert_eq!(out[j],(if j<len{{initial[j]}}else{{source[j-len]}})^NEG);
'''
def bodywindow(lo,hi):
 return f'''let initial:[u8;1736]=kani::any();let source:[u8;32]=kani::any();
let mut out=alloc::vec::Vec::from(initial);
KMX_stubs::KMX_extend_from_slice(&mut out,&source);
assert_eq!(out.len(),1768);assert_eq!(out.capacity(),3472);
let j:usize=kani::any();kani::assume({lo}<=j && j<{hi});
assert_eq!(out[j],(if j<1736{{initial[j]}}else{{source[j-1736]}})^NEG);
'''
def draft(name,lo=None,hi=None):
 s=(PREV/'drafts'/('KMZ_'+name+'.rs')).read_text()
 s=s[s.index('fn KMZ_put_k'):] if name=='selected' else s[s.index('#[kani::proof]'):]
 s=s.replace('KMZ_','KNA_').replace(' ^ 0u8',' ^ NEG')
 if name=='selected':s=s.replace('assert_eq!(out[j],if j<len{initial[j]}else{raw[(j-len)/4].to_le_bytes()[(j-len)%4]});','assert_eq!(out[j],(if j<len{initial[j]}else{raw[(j-len)/4].to_le_bytes()[(j-len)%4]}) ^ NEG);')
 if lo is not None:s=s.replace('kani::assume(j<out.len());',f'kani::assume(j<out.len() && {lo}<=j && j<{hi});')
 return BASE+s

def invoke(name,source,negative,parent=None):
 n=len(list(E.glob('KNA_K[0-9][0-9][0-9].json')))+1
 if n>90:return 'BUDGET'
 a=f'KNA_K{n:03}'
 src=source.replace('NEG','1u8' if negative else '0u8')
 import re
 h=re.findall(r'fn (KNA_\w+)\(\)',src)[-1]
 cfg=json.loads((PREV/'KMZ_K069.json').read_text())
 cfg.update(sources=['KNA_windows.rs','KMX_stubs.rs','KMY_src/Cargo.lock','KNA_gate.py','KMY_field.rs','KMY_wide_exact.rs'],command=['python3','KNA_gate.py',a,h],negative_control=negative,split=name,parent_gate=parent,expected_time='optimized codegen then '+name+' selected-window CBMC')
 return run(a,cfg,src)

def pair(name,source):
 records=json.loads((E/'KNA_PAIRS.json').read_text()) if (E/'KNA_PAIRS.json').exists() else []
 if any(x['name']==name for x in records):return next(x for x in records if x['name']==name)
 before=len(list(E.glob('KNA_K[0-9][0-9][0-9].json')))+1
 if before>89:return dict(name=name,positive='BUDGET',control='BUDGET')
 pos=invoke(name,source,False);neg=invoke(name,source,True,f'KNA_K{before:03}')
 row=dict(name=name,positive=pos,control=neg,positive_id=f'KNA_K{before:03}',control_id=f'KNA_K{before+1:03}',credit=pos=='PASS' and neg=='COUNTEREXAMPLE')
 records.append(row);(E/'KNA_PAIRS.json').write_text(json.dumps(records,indent=2)+'\n')
 if 'ERROR' in [pos,neg]:raise SystemExit('Inspect own input or host error: '+name)
 if pos=='COUNTEREXAMPLE' or neg=='PASS':raise SystemExit('FIRST failed positive or passing control: '+name)
 return row

def main():
 # Exact prescribed next splits before adaptive replacements.
 for cap,lo,hi in [(128,1,16),(256,17,22)]:
  pair(f'query_{lo}_{hi}',BASE+ATTR.replace('1769','258')+f'fn KNA_query_{lo}_{hi}(){{'+query(cap,lo,hi)+'}\n')
 for w in range(12):
  lo=160*w if w<11 else 1736;hi=min(1736,lo+160) if w<11 else 1768
  pair(f'body_{lo}_{hi}',BASE+ATTR+f'fn KNA_body_{lo}_{hi}(){{'+bodywindow(lo,hi)+'}\n')
 for name in ['selected','append32','append4','append16']:pair(name,draft(name))
 # Any 160-byte timeout is replaced by halves, never rerun unchanged.
 for w in range(11):
  lo=160*w;hi=min(1736,lo+160)
  r=next(x for x in json.loads((E/'KNA_PAIRS.json').read_text()) if x['name']==f'body_{lo}_{hi}')
  if not r['credit']:
   mid=(lo+hi)//2
   for a,b in [(lo,mid),(mid,hi)]:pair(f'body_{a}_{b}',BASE+ATTR+f'fn KNA_body_{a}_{b}(){{'+bodywindow(a,b)+'}\n')
 # Split remaining symbolic-length gates by observed byte, not by length enumeration.
 for name in ['selected','append32','append4','append16']:
  for lo,hi in [(0,884),(884,1768)]:pair(f'{name}_byte_{lo}_{hi}',draft(name,lo,hi))
if __name__=='__main__':main()
