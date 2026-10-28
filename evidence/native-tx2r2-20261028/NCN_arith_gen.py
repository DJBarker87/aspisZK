from NCN_extend import extend,attrs,E
import json
h='\n#[cfg(kani)] mod NCN_arith {\nuse super::*;\n'
qs=[]
for stage in ['product','add']:
 for neg in [False,True]:
  name=stage+('_wrong' if neg else '_ok')
  h+=attrs+f'fn {name}(){{\n'
  if stage=='product':
   h+='let a:u32=kani::any();let b:u32=kani::any();let x=u64::from(a);let y=u64::from(b);let result=x*y;\n'
   # Reference widening/cast identity only, not an independent multiplier equivalence.
   h+=f'assert!(result{"!=" if neg else "=="}(a as u64)*(b as u64));\n'
  else:
   h+='''let mut row:[u64;4]=kani::any();let product:u64=kani::any();let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<4&&k<4&&k!=j);
kani::assume(row[j]<=u64::MAX-product);let before=row[j];let frame=row[k];row[j]=before+product;
'''
   h+=f'assert!(row[j]{"!=" if neg else "=="}before+product);assert!(row[k]==frame);\n'
  h+='}\n';qs.append(dict(harness='verifier::NCN_arith::'+name,negative=neg))
h+='}\n';extend('NCN_arith.patch',h)
for i,q in enumerate(qs,27):q.update(attempt=f'NCN_K{i:03}',patch='NCN_arith.patch')
(E/'NCN_arith_queue.json').write_text(json.dumps(qs,indent=2)+'\n')
