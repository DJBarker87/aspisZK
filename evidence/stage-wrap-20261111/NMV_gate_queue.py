"""Own focused formal gate; canonical tools and admission remain unchanged."""
from NMV_formal import *
import re,lzma

def manifests():
 mods=['NMV_Snapshot','NMV_Model','NMV_Stage1','NMV_Stage2','NMV_TotalSnapshot','NMV_TotalFold','NMV_TotalStage2','NMV_TotalStage1','NMV_Carriers','NMV_RslLaws','NMV_RslSnapshots','NMV_RslDomain','NMV_RslFold','NMV_G2','NMV_FullState','NMV_SdkFrame','NMV_G2State','NMV_Stage1Frame','NMV_WeakFold','NMV_PhysicalCarrier']
 groups=[];selected=[]
 for m in mods:
  s=(E/(m+'.lean')).read_text();ns=re.search(r'^namespace (\S+)',s,re.M)[1]
  th=re.findall(r'^theorem (\w+)',s,re.M);prints=re.findall(r'^#print axioms (\w+)',s,re.M)
  assert set(th)==set(prints),(m,th,prints)
  names=[ns+'.'+n for n in th]
  if m!='NMV_PhysicalCarrier' and groups and len(groups[-1])+len(names)<=8:
   groups[-1].extend(names);selected[-1].append(m)
  else:
   groups.append(names);selected.append([m])
 (E/'NMV_AUDIT_ROOTS.json').write_text(json.dumps({'groups':groups,'roots':[r for g in groups for r in g]},indent=1)+'\n')
 (E/'NMV_AUDIT_MODULES.json').write_text(json.dumps(selected,indent=1)+'\n')
 return mods,groups

def checked(a,n):
 r=run(a,'lean',n)
 if r['exit_status']:raise SystemExit(r['exit_status'])

if __name__=='__main__':
 mode=sys.argv[1]
 if mode=='compile':
  for a,n in [('NMV_L059','NMV_Carriers'),('NMV_L060','NMV_WeakFold')]:checked(a,n)
 elif mode=='combined':
  mods,_=manifests()
  (E/'NMV_COMBINED_IMPORT.lean').write_text('import NLX_COMBINED_IMPORT\n'+''.join('import '+n+'\n' for n in mods)+'\n#print axioms AspisR1.RPx_Deployed.deployed\n')
  checked('NMV_L061','NMV_COMBINED_IMPORT')
 elif mode=='final-combined':
  mods,_=manifests()
  (E/'NMV_COMBINED_IMPORT.lean').write_text('import NLX_COMBINED_IMPORT\n'+''.join('import '+n+'\n' for n in mods)+'\n#print axioms AspisR1.RPx_Deployed.deployed\n')
  checked('NMV_L077','NMV_COMBINED_IMPORT')
 elif mode=='supplement':
  _,groups=manifests();assert len(groups)==12
  files={n:(E/n).read_text() for n in ['NMV_batch.py','NMV_AUDIT_ROOTS.json','NMV_AUDIT_MODULES.json']}
  r=run('NMV_L078','audit','proof11',['python3','NMV_batch.py','proof11'],files)
  if r['exit_status']:raise SystemExit(r['exit_status'])
 elif mode=='driver':
  manifests();checked('NMV_L062','NMV_ProofDriver')
 elif mode=='link':
  extra={}
  for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
   extra['NMV_native/'+n]=lzma.decompress((E.parent/'tx2-entry5-20261110/NMN_native'/(n+'.xz')).read_bytes()).decode()
  env=json.loads((E/'NMV_ENV.json').read_text())
  r=run('NMV_L063','link','NMV_ProofDriver',[env['LEAN_SYSROOT']+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NMV_native/NMV_ProofDriver','NMV_native/NMV_ProofDriver.c','NMV_native/NFA_WALKER.c','NMV_native/NFA_MemoryLimit.c'],extra)
  if r['exit_status']:raise SystemExit(r['exit_status'])
 elif mode=='proofs':
  _,groups=manifests()
  for i in range(len(groups)):
   a=f'NMV_L{65+i:03}'
   files={n:(E/n).read_text() for n in ['NMV_batch.py','NMV_AUDIT_ROOTS.json','NMV_AUDIT_MODULES.json']}
   r=run(a,'audit','proof'+str(i),['python3','NMV_batch.py','proof'+str(i)],files)
   if r['exit_status']:raise SystemExit(r['exit_status'])
 elif mode=='fixtures':
  r=run('NMV_L064','audit','fixtures',['python3','NMV_batch.py','fixtures'],{'NMV_batch.py':(E/'NMV_batch.py').read_text()})
  if r['exit_status']:raise SystemExit(r['exit_status'])
 else:raise ValueError(mode)
