"""Twelve compression blocks per module, including cross-window leaf chaining.
Uses inherited symbolic padding/round emitter without executing its old campaign.
"""
from pathlib import Path
import json,sys,hashlib,re
P=Path(__file__).resolve().parent;R=P.parents[1]
base=(R/'evidence/joint-fixture11-20261026/JFm_generate.py').read_text().split('raw=[]')[0].replace('len(msg)<256','len(msg)<64')
env={'__file__':str(R/'evidence/joint-fixture11-20261026/JFm_generate.py')};exec(base,env)
files={};plans=[]
data=json.loads((P/'JGr_BATCH0_PREFLIGHT.json').read_text())
old=json.loads((R/'evidence/fixture-tx2j-20261027/JGf_MERKLE_PREFLIGHT.json').read_text())
reuse={}
for ot in old['trees']:
 ns=['JGf_TX2_M0Roots','JGh_TX2_M1Roots','JGc_TX2_M2Roots'][ot['tree']]
 root=['JGf_TX2_M0Root','JGh_TX2_M1Root','JGc_TX2_M2Root'][ot['tree']]
 for oi,rr in enumerate(ot['hashes']):reuse[bytes(rr['message'])]=dict(namespace=ns,index=oi,module=root)
for tree in data['trees']:
 t=tree['tree'];units=[];owners={}
 for i,row in enumerate(tree['hashes']):
  if bytes(row['message']) in reuse:
   row['reuse']=reuse[bytes(row['message'])];continue
  name=f'JGr_M{t}.Hash{i:03}'
  digest=env['cert'](name,bytes(row['message']));assert list(digest)==row['digest']
  text=env['files'][R/'lean'/(name+'.lean')]
  prefix=f'namespace AspisR1.{name}\nopen JFp_SHA256\n'
  matches=list(re.finditer(r'namespace B\d\d\n.*?end B\d\d\n',text,re.S));assert len(matches)==row['blocks']
  footer=text[matches[-1].end():];assert footer.endswith(f'end AspisR1.{name}\n')
  for bi,m in enumerate(matches):
   body=prefix+m.group(0)
   body+=footer if bi==len(matches)-1 else f'end AspisR1.{name}\n'
   units.append(dict(hash=i,block=bi,body=body,final=bi==len(matches)-1))
 for off in range(0,len(units),12):
  group=units[off:off+12];module=f'JGr_M{t}C{off//12:03}'
  prev=f'JGr_M{t}C{off//12-1:03}' if off else 'JFp_SHABlocks'
  s='import '+prev+'\nset_option autoImplicit false\n'+''.join(u['body'] for u in group)
  files[R/'lean'/(module+'.lean')]=s
  for u in group:
   if u['final']:owners[u['hash']]=module
  plans.append(dict(module=module,tree=t,blocks=len(group),units=[{k:v for k,v in u.items() if k!='body'} for u in group]))
 tree['owners']=owners
files[P/'JGr_HASH_PLAN.json']=json.dumps(plans,indent=2)+'\n'
files[P/'JGr_MERKLE_PREFLIGHT.json']=json.dumps(data,indent=2)+'\n'
for f,s in files.items():
 if '--check' in sys.argv:
  retained=f if f.exists() else P/'JGf_UNCHECKED'/(f.name+'.txt')
  assert retained.read_text()==s,retained
 else:f.write_text(s)
print('preflight:',len(plans),'window modules;',sum(x['blocks'] for x in plans),'blocks; max12; next consumer JGr_M0Leaves and symbolic tree root, then native batch0')
