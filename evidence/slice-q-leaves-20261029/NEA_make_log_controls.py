from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));from NEA_payload import save
p=json.loads((E/'NEA_PAYLOAD.json').read_text());key='crates/aspis-r1-cost-probe/src/NEA_fold.rs';s=p[key]
for name,fn,T,U,V,N in [('EM','em','E','E','E',3),('SM','sm','E','M31','E',6),('BM','bm','M31','M31','M31',4)]:
 for mode in ['repeat','pair','full']:
  count=N if mode=='full' else 2
  h=f'{fn}_{mode}'
  s+='\n#[kani::proof]\n#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEA_copy::KMX_copy_nonoverlapping)]\nfn '+h+'(){unsafe{reset();}\n'
  for i in range(count):
   if mode=='repeat' and i==1:s+='let x1=x0;let y1=y0;\n'
   else:
    s+=f'let x{i}='+('any_e();' if T=='E' else 'M31(kani::any());')+'\n'
    if U=='E':s+=f'let y{i}=any_e();\n'
    elif name=='SM':s+=f'let w{i}:u32=kani::any();kani::assume(w{i}<P);let y{i}=M31(w{i});\n'
    else:s+=f'let y{i}=M31(kani::any());\n'
   s+=f'let r{i}={fn}(x{i},y{i});\n'
  terms=[f'{name}.count=={count}']
  for i in reversed(range(count)):
   terms += [f'{fn}_replay(x{i},y{i})==r{i}',f'{name}.slots[{i}].x==x{i}',f'{name}.slots[{i}].y==y{i}',f'{name}.slots[{i}].out==r{i}',f'canon(r{i})' if V=='E' else f'r{i}.0<P']
  terms += [f'{name}.count=={count}']
  if mode=='repeat':terms+=['r0==r1']
  s+='let valid=unsafe{'+ '&&'.join(terms)+'};assert!(valid != cfg!(NEA_wrong_log));}\n'
p[key]=s;save(p);(E/'NEA_log_controls.rs.txt').write_text(s)
