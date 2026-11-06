from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent;read=lambda n:json.loads((E/n).read_text());std={'propext','Classical.choice','Quot.sound'}
ats=[json.loads(l) for l in (E/'PCE_ATTEMPTS.jsonl').read_text().splitlines()];by={a['attempt']:a for a in ats}
for i in [1,4,5,6,8]+list(range(9,25)):assert by[f'PCE_L{i:03d}']['exit_status']==0,i
binary=read('PCE_binary_fixtures.json')['sha256'];fixtures=read('PCE_binary_fixtures.json')['results'];assert len(fixtures)==8
assert all(x['equal'] and len(x['walked_axioms'])==(1 if i<4 else 0) for i,x in enumerate(fixtures))
roots=[];disagreements=[];attempts={}
for i,g in enumerate(read('PCE_GROUPS.json')):
 mode='roots'+str(i);x=read('PCE_binary_'+mode+'.json');assert x['sha256']==binary and x['unchanged'] and x['policy_exit']==0
 assert [r['root'] for r in x['results']]==g
 for r in x['results']:
  assert set(r['walked_axioms'])<=std,r
  if not r['equal'] or r['collect_axioms']!=r['walked_axioms']:disagreements.append(dict(r,ruling="(ab')(3)/(c-d): raw walk authoritative; standard-only collector disagreement is tooling finding"))
  attempts[r['root']]=f'PCE_L{9+i:03d}'
 roots+=x['results']
assert [r['root'] for r in roots]==read('PCE_ROOTS.json')['roots']
scan=[json.loads(l) for l in lzma.decompress((E/'PCE_LOADED_scan.jsonl.xz').read_bytes()).decode().splitlines()];assert scan and all(not x['dangling'] and not x.get('duplicate_owners',[]) and x['imports_match'] for x in scan)
s=dict(status='PASS',attempt='PCE_L008',modules=len(scan),dangling=0,duplicate_owners=0,incompatible_owners=0,import_defects=0,identical_cached_replicas=sum(len(x.get('cached_replicas',[])) for x in scan),source='PCE_LOADED_scan.jsonl.xz',raw_sha256=(E/'PCE_LOADED_scan.jsonl.sha256').read_text().strip(),binary_sha256=read('PCE_binary_scan.json')['sha256']);assert s['binary_sha256']==binary
(E/'PCE_SCAN.json').write_text(json.dumps(s,indent=1)+'\n')
statements={};chunk=[]
for l in (E/'PCE_L022/stdout.log').read_text().splitlines():
 if l.startswith('{'):
  x=json.loads(l)
  if 'type_expr' in x:
   statements[x['root']]=dict(x,checked_statement='\n'.join(chunk).strip(),type_expr_sha256=hashlib.sha256(x['type_expr'].encode()).hexdigest());chunk=[]
 else:chunk.append(l)
assert set(statements)==set(read('PCE_ROOTS.json')['roots']),('statement count',len(statements))
(E/'PCE_STATEMENTS.json').write_text(json.dumps(statements,indent=1)+'\n')
a=dict(status='PASS',headline='AspisR1.RPx_Deployed.deployed',combined='PCE_L001',scan='PCE_SCAN.json',roots=roots,root_attempts=attempts,root_count=len(roots),fixtures=fixtures,fixture_attempt='PCE_L006',binary_sha256=binary,collector_disagreements=disagreements,raw_authority="(ab')(3)/(c-d)",standard_axioms=sorted(std),native='REUSED only; PCE_NATIVE_VALIDATION.json',provenance='PCE_FINAL_PINS.json',recompiled_existing_modules=[],new_modules=['PCE_COMBINED_IMPORT','PCE_AuditDriver','PCE_Statements'],unchanged_PCB_common_objects=read('PCE_PCB_OBJECT_COMPARISON.json'),scope='Focused cached composition, not cold release replay; no parent Pool or security-target closure',source_revision=by['PCE_L001']['source_revision'])
(E/'PCE_AUDIT.json').write_text(json.dumps(a,indent=1)+'\n')
print('Stage1 gate PASS: '+str(len(roots))+' raw-standard roots; '+str(len(disagreements))+' retained collector disagreements; zero scan defects.')
