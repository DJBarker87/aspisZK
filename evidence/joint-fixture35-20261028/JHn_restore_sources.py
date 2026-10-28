from pathlib import Path
import json,re,hashlib,sys
def emit(p,s):
 if "--check" in sys.argv:
  assert p.read_text()==s,str(p)
 else:p.write_text(s)
P=Path(__file__).resolve().parent;R=P.parents[1]
d=json.loads((P/'JHn_DEPENDENCIES.json').read_text())
missing=[m for m in d['order'] if d['objects'][m] is None and not m.startswith('JHn_')]
mapping={m:'JHn_R_'+m for m in missing}
manifest=[];order=[]
for old in missing:
 s=(R/'lean'/(old+'.lean')).read_text();new=mapping[old]
 for a,b in mapping.items():s=re.sub(r'^import '+re.escape(a)+r'$', 'import '+b,s,flags=re.M)
 if old=='JHh_C_Tree0B_L0':
  imports=s[:s.index('section\n')]
  units=[]
  for i in range(5):
   namespace=f'AspisR1.JHh_C_Gu_M0Leaf{i:02}'
   start=s.index('namespace '+namespace+'\n');end=s.index('end '+namespace+'\n',start)+len('end '+namespace+'\n')
   name=f'JHn_R_M0Leaf{i:02}'
   text=imports+'section\nvariable [sha : AspisR1.JHe_SHARealization]\nset_option autoImplicit false\nset_option linter.unusedSimpArgs false\nnoncomputable section\n'+s[start:end]+'end\nend\n'
   emit(R/'lean'/(name+'.lean'),text);units.append(name);order.append(name)
  s='\n'.join('import '+m for m in units)+'\n'
  # Keep all reconstructed declarations in their original namespaces.
 emit(R/'lean'/(new+'.lean'),s);order.append(new)
 manifest.append(dict(original=old,module=new,original_sha256=hashlib.sha256((R/'lean'/(old+'.lean')).read_bytes()).hexdigest(),new_sha256=hashlib.sha256(s.encode()).hexdigest(),change='imports only' if old!='JHh_C_Tree0B_L0' else 'split into five independent previously proved leaf namespaces; no monolithic timed-out rerun'))
emit(P/'JHn_RESTORE_PLAN.json',json.dumps(dict(mapping=mapping,order=order,sources=manifest),indent=2)+'\n')
print('New-prefix missing-cache restoration:',len(order),'modules')
