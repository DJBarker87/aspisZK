"""Each native child runs sequentially and has independent time/RSS/axiom receipt."""
from pathlib import Path
import subprocess,json,time,hashlib,re,sys,lzma
B=Path.cwd();mode=sys.argv[1];E=B/'NKA_audit'/mode;E.mkdir(parents=True,exist_ok=True)
if mode.startswith('inventory-'):jobs=[(mode,['NKA_native/NKA_InventoryDriver',mode.split('-')[1]])]
elif mode in ['poolfixtures','poolroots','poolscan']:jobs=[('scan' if mode=='poolscan' else 'fixtures' if mode=='poolfixtures' else 'proof0',['NKA_native/'+('NKA_PoolDriver' if mode=='poolscan' else 'NKA_PoolProofDriver'), 'scan' if mode=='poolscan' else 'fixtures' if mode=='poolfixtures' else 'proof0'])]
elif mode in ['fixtures','scan']:jobs=[(mode,['NKA_native/'+('NKA_Driver' if mode=='scan' else 'NKA_ProofDriver'),mode])]
else:
 batch=int(mode.removeprefix('batch'));groups=json.loads((B/'NKA_AUDIT_ROOTS.json').read_text())['groups'];jobs=[('proof'+str(i),['NKA_native/NKA_ProofDriver','proof'+str(i)]) for i in range(batch,min(batch+1,len(groups)))];assert jobs
for name,command in jobs:
 start=time.monotonic()
 with (E/(name+'.log')).open('w') as out:r=subprocess.run(['/usr/bin/time','-v','-o',str(E/(name+'.time')),*command],stdout=out,stderr=subprocess.STDOUT)
 raw=(E/(name+'.log')).read_text();timing=(E/(name+'.time')).read_text()
 def metric(k):
  m=re.search(re.escape(k)+r':\s*(.*)',timing);return m[1] if m else None
 receipt=dict(target=name,command=command,exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),print_axioms=[l for l in raw.splitlines() if 'depends on axioms' in l or 'does not depend on any axioms' in l],results=[json.loads(l[11:]) for l in raw.splitlines() if l.startswith('NEP_RESULT ')])
 archives=B/'NKA_archives';archives.mkdir(exist_ok=True)
 for source in sorted(B.glob('NEP_'+name+'_*')):
  if not source.is_file():continue
  rawbytes=source.read_bytes();target=archives/(source.name+'.xz')
  target.write_bytes(lzma.compress(rawbytes,preset=6))
  (archives/(source.name+'.sha256')).write_text(hashlib.sha256(rawbytes).hexdigest()+'\n')
  source.unlink()
 results=receipt['results']; policy=True
 if mode=='fixtures':
  expected={'NEP_Planted.matcher':['NEP_Planted.matchAx'],'NEP_Planted.viaPrivate':['NEP_Planted.privateAx'],'NEP_Planted.proof':['NEP_Planted.proofAx'],'NEP_Planted.viaAux':['NEP_Planted.auxAx'],'NEP_MutateMatch.matcher':[],'NEP_MutatePrivate.viaPrivate':[],'NEP_MutateProof.proof':[],'NEP_MutateAux.viaAux':[]}
  policy=len(results)==8 and {z['root']:z['walked_axioms'] for z in results}==expected and all(z['equal'] and z['walked_axioms']==z['collect_axioms'] for z in results)
 elif mode.startswith('batch'):
  wanted=json.loads((B/'NKA_AUDIT_ROOTS.json').read_text())['groups'][int(mode.removeprefix('batch'))]
  policy=[z['root'] for z in results]==wanted and all(z['equal'] and set(z['walked_axioms'])<= {'propext','Classical.choice','Quot.sound'} and z['walked_axioms']==z['collect_axioms'] for z in results)
 elif mode=='scan':policy='NFN_SCAN_ZERO_DANGLING' in raw
 receipt['policy_pass']=policy
 (E/(name+'.json')).write_text(json.dumps(receipt,indent=1)+'\n');print(json.dumps(dict(target=name,exit_status=r.returncode,policy_pass=policy,roots=len(results))),flush=True)
 if not policy:sys.exit(1)
 if r.returncode:print(raw,flush=True);sys.exit(r.returncode)
