from pathlib import Path
import subprocess,re,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2e-20261029';P=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';x=json.loads((E/'fallback-resolution.json').read_text())
shared={'R1Z.PV_CBL_ArrayKernel','R1Z.PV_CBL_ArrayStep'}
groups=[]
const=[m for m in x['order']if re.search(r'FallbackConstant',m)]
lanes=[m for m in x['order']if re.search(r'Fallback(?:Lane|SmallSigma)',m)]
canonical=[m for m in x['order']if m.split('.')[-1]in ['PV_CBL_FallbackBoolean','PV_CBL_FallbackAddAlgebra','PV_CBL_FallbackCanonicalT1','PV_CBL_FallbackCanonicalT2','PV_CBL_FallbackCanonicalStep']]
# Groups are emitted at their last component so every dependency stays earlier.
combined=[('FallbackConstants',const),('FallbackLanes',lanes),('FallbackCanonical',canonical)]
last={vs[-1]:(name,vs)for name,vs in combined};grouped={m for _,vs in combined for m in vs}
for m in x['order']:
 if m in shared:continue
 if m in last:groups.append(last[m])
 elif m not in grouped:groups.append((m.split('.')[-1].replace('PV_CBL_',''),[m]))
mapping={m:'R1Z.PV_RDB2E_'+n for n,ms in groups for m in ms};mapping.update({m:'R1Z.PV_RDB2D_SHAModel'for m in shared})
records=[]
def clean(s):
 s=re.sub(r'/--.*?-/|/-.*?-/',lambda m:'\n'*m[0].count('\n'),s,flags=re.S);return re.sub(r'--[^\n]*','',s)
for name,ms in groups:
 bodies=[];imports=[];components=[]
 for m in ms:
  r=x['modules'][m];raw=subprocess.check_output(['git','show',r['blob']]);assert hashlib.sha256(raw).hexdigest()==r['sha256'];s=raw.decode()
  for imp in r['imports']:
   dep=mapping.get(imp,imp)
   if imp not in ms and dep not in imports:imports.append(dep)
  s=re.sub(r'^import .*\n','',s,flags=re.M);stack=[]
  for line in clean(s).splitlines():
   t=line.strip()
   if re.match(r'namespace\s|(?:noncomputable\s+)?section\b',t):stack.append(t)
   elif re.match(r'end(?:\s|$)',t):assert stack,(m,t);stack.pop()
  bodies.append('section\n-- Unchanged source component '+m+'\n'+s+'\n'+'end\n'*len(stack)+'end\n')
  components.append(dict(module=m,source=r,changes='imports only and local section scopes; declarations, statements, proofs, options unchanged'))
 text=''.join('import '+dep+'\n'for dep in imports)+'\n'+'\n'.join(bodies)
 target=P/('PV_RDB2E_'+name+'.lean');target.write_text(text)
 records.append(dict(module='R1Z/PV_RDB2E_'+name,components=components,imports=imports,source_sha256=hashlib.sha256(text.encode()).hexdigest()))
(E/'fallback-owned.json').write_text(json.dumps(records,indent=2));print('owned fallback focused targets',len(records))
