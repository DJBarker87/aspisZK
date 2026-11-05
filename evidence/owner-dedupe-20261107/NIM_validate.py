from pathlib import Path
import json,hashlib,lzma,subprocess,collections
E=Path(__file__).resolve().parent
read=lambda p:json.loads(p.read_text())
rs=[json.loads(l)for l in (E/'NIM_ATTEMPTS.jsonl').read_text().splitlines()]
assert len(rs)==40 and len({r['attempt']for r in rs})==40
assert collections.Counter(r['kind']for r in rs)=={'lean':29,'link':2,'audit':9}
for r in rs:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert int(r['swaps'])==0 and int(r['peak_rss_kib'])<8*1024*1024
 ad=read(E/(r['attempt']+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert r['timeout']==180
 if r['kind']=='lean':assert '-M7000' in r['command']
 if r['kind']=='link':assert '-O3' in r['command']
for a in ['NIM_L001','NIM_L006','NIM_L010','NIM_L026','NIM_L039','NIM_L040']:assert read(E/a/'receipt.json')['exit_status']==1
assert all(r['exit_status']==0 for r in rs if r['attempt'] not in ['NIM_L001','NIM_L006','NIM_L010','NIM_L026','NIM_L039','NIM_L040'])
roots=read(E/'NIM_AUDIT_ROOTS.json')['roots'];seen=[];standard={'propext','Classical.choice','Quot.sound'};binary=read(E/'NIM_L032/NIM_ProofDriver_BINARY_PIN.json')['sha256']
for i in range(7):
 a=f'NIM_L{34+i:03}';x=read(E/'NIM_audit'/('batch'+str(i))/('proof'+str(i)+'.json'));assert x['exit_status']==(1 if i in [5,6]else 0)
 assert read(E/a/'NIM_ProofDriver_BINARY_PIN.json')['sha256']==binary
 for r in x['results']:
  assert set(r['walked_axioms'])<=standard,r
  if not r['equal']:assert r['root']=='NHC_DecodeModel.decoder_error'and r['collect_axioms']==[]
  seen.append(r['root'])
required=read(E/'NIM_AUDIT_ROOTS_CORRECTED.json')['roots']
assert set(required)<=set(seen) and len(set(seen))==len(seen)
assert len(set(roots)-set(seen))==103 and not(set(roots)-set(seen))&set(required)
f=read(E/'NIM_audit/fixtures/fixtures.json');assert f['exit_status']==0 and len(f['results'])==8
expected=[['NEP_Planted.matchAx'],['NEP_Planted.privateAx'],['NEP_Planted.proofAx'],['NEP_Planted.auxAx'],[],[],[],[]]
for r,w in zip(f['results'],expected):assert r['equal'] and r['walked_axioms']==r['collect_axioms']==w
s=read(E/'NIM_SCAN.json');assert s['exit_status']==s['dangling']==s['incompatible_owners']==s['import_mismatches']==0
for p in ['NHJ','NHY']:assert read(E/('NIM_REPLAY_'+p+'.json'))['exit_status']==0
assert all(x['selected']for x in read(E/'NIM_CERTIFICATE_ROOTS.json'))
subprocess.run(['python3',str(E/'NIM_generate.py'),'--check'],check=True)
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20*1024*1024,p
assert not list(E.rglob('__pycache__'))
print(json.dumps(dict(status='PASS',slots=40,required_roots=len(required),measured_roots=len(seen),retained_nonzero_audit_exits=['NIM_L039','NIM_L040'],same_binary_sha256=binary,fixture_results=8,scan=s)))
