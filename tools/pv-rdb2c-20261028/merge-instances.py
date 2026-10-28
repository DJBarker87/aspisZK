from pathlib import Path
import subprocess,json,re,hashlib
R=Path(__file__).resolve().parents[2];P=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-rdb2c-20261028'
def git(key):return subprocess.check_output(['git','show',key],cwd=R)
def clean(s):
 s=re.sub(r'/--.*?-/|/-.*?-/',lambda m:'\n'*m[0].count('\n'),s,flags=re.S)
 return re.sub(r'--[^\n]*','',s)
def merge(label,entries,extra):
 body=[];records=[];external=[];own={m for m,r in entries}
 for m,r in entries:
  raw=git(r['blob']);assert hashlib.sha256(raw).hexdigest()==r['sha256']
  s=raw.decode();imports=re.findall(r'^import (\S+)',s,re.M)
  for dep in imports:
   if dep not in own and dep not in external:external.append(dep)
  s=re.sub(r'^import .*\n','',s,flags=re.M)
  stack=[]
  for line in clean(s).splitlines():
   x=line.strip()
   if re.match(r'namespace\s|(?:noncomputable\s+)?section\b',x):stack.append(x)
   elif re.match(r'end(?:\s|$)',x):
    assert stack,(m,x);stack.pop()
  body.append('section\n-- Unchanged source component: '+m+'\n'+s+'\n'+'end\n'*len(stack)+'end\n')
  records.append(dict(module=m,authority=r,sha256=r['sha256'],changes='imports removed into common header; file-local section scope preserved explicitly; every declaration and proof text unchanged'))
 imports=list(dict.fromkeys(extra+external));text=''.join('import '+m+'\n' for m in imports)+'\n'+'\n'.join(body)
 (P/(label+'.lean')).write_text(text);(E/(label+'-components.json')).write_text(json.dumps(dict(components=records,imports=imports,source_sha256=hashlib.sha256(text.encode()).hexdigest()),indent=2)+'\n')
j=json.load(open(E/'samplers-resolution.json'));entries=[(m,j['modules'][m]) for m in j['order'] if j['modules'][m]['authority']=='h5 own HEAD']
merge('PV_RDB2C_SamplerInstance',entries,[])
ms=['PV_B2_F_MaterializeNative','PV_B2_F_251Bridge','PV_B2_F_ConstructorCarrier','PV_B2_F_ConstructorCarrierLaws','PV_B2_F_ConstructorEffect','PV_B2_F_ConstructorNative'];entries=[]
for n in ms:
 p='docs/research/v8-r0-zk-20261009/lean/R1Z/'+n+'.lean';blob=subprocess.check_output(['git','rev-parse','HEAD:'+p],text=True).strip();raw=git(blob);entries.append(('R1Z.'+n,dict(path=p,blob=blob,sha256=hashlib.sha256(raw).hexdigest(),authority='h5 own HEAD')))
merge('PV_RDB2C_WeightsInstance',entries,['R1Z.PV_RDB2C_SamplerInstance','R1Z.PV_RDB2C_PV_B2_F_MaterializeRequest','R1Z.PV_RDB2C_PV_B2_C_ConstructorSuccess'])
# Replace only import bindings to the already compiled owned modules. No
# dictionary, callback, observer or proof declaration body is edited.
p=P/'PV_RDB2C_WeightsInstance.lean';s=p.read_text()
for n in ['PV_B2_F_AllocationEffects','PV_B2_F_MaterializeFrozen']:
 s=s.replace('import R1Z.'+n+'\n','import R1Z.PV_RDB2C_'+n+'\n')
for n in ['PV_B2_E_GammaOriginal','PV_B2_E_OrdinaryOriginal']:
 s=s.replace('import R1Z.'+n+'\n','')
s=s.replace('import R1Z.PV_B2_C_ConstructorSuccess\n','')
s=s.replace('import R1Z.PV_B2_F_MaterializeRequest\n','')
p.write_text(s)
# Pin final bytes after import narrowing.
q=E/'PV_RDB2C_WeightsInstance-components.json';r=json.load(open(q));r['owned_source_sha256']=hashlib.sha256(s.encode()).hexdigest();r['final_imports']=re.findall(r'^import (\S+)',s,re.M);q.write_text(json.dumps(r,indent=2)+'\n')
print('merged',len(entries),'weight callback components and nine sampler/carrier components')
