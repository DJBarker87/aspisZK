from pathlib import Path
import json,re,hashlib,lzma,subprocess,datetime
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2e-20261029';P=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
plan=json.loads((E/'frozen-proof-manifest.json').read_text());allowed={'propext','Classical.choice','Quot.sound'};rows=[]
for n in range(62200,62300):
 p=E/f'lean-{n}/receipt.json';j=json.loads(p.read_text());assert j['attempt']==n and j['swap']=='0'
 assert hashlib.sha256(subprocess.check_output(['git','show',j['source_blob']])).hexdigest()==j['source_sha256'],n
 m=j['module'].replace('/','.');audit=n>=62297
 credit=j['exit']==0 and (m in plan['modules']or audit)
 if credit:
  if m in plan['modules']:assert j['source_sha256']==plan['modules'][m]['source_sha256'],n
  for ax in j['print_axioms']:
   s=re.search(r'depends on axioms: \[([^]]*)\]',ax,re.S)
   if s:assert {a.strip()for a in s[1].split(',')}<=allowed,(n,ax)
 for f in ['admission-before.json','admission-launch.json','admission-barrier.json']:
  a=json.loads((p.parent/f).read_text());assert a['allowed']is True,(n,f)
 j['dependency_fingerprint']='dependency-fingerprint.json.xz'if credit else None
 j['formal_credit_scope']='independent checked model cohort; no native row closure'if credit else 'not in final independent cohort or failed elaboration; no credit'
 p.write_text(json.dumps(j,indent=2)+'\n')
 rows.append(dict(attempt=n,module=j['module'],target=j['target'],exit=j['exit'],wall=j['wall'],peak_rss_kib=j['peak_rss_kib'],swap=j['swap'],source_revision=j['source_revision'],source_sha256=j['source_sha256'],source_blob=j['source_blob'],print_axioms=j['print_axioms'],independent_cohort_credit=credit,receipt=str(p.relative_to(E))))
raw=lzma.decompress((E/'dependency-fingerprint.json.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==(E/'dependency-fingerprint.json.sha256').read_text().strip();fp=json.loads(raw)
assert all(r['ok']for r in fp['external']+fp['native_source_checks']+fp['registry_source_checks'])
assert not fp['shared_sent_collisions']
assert all(not d['module'].startswith('AspisR72Sampler')for r in fp['objects']for d in r['imports'])
for r in json.loads((E/'final-audit-objects.json').read_text()):
 receipt=json.loads((E/f"lean-{r['attempt']}/receipt.json").read_text());assert r['source_sha256']==receipt['source_sha256']and receipt['exit']==0
native=[]
for name,script in [('preflight','preflight.py'),('native-associations','native.py'),('native-associations-lock-fixed','native.py'),('final-fingerprint','fingerprint.py'),('final-cleanup','cleanup.py')]:
 p=E/name/'receipt.json';j=json.loads(p.read_text());assert j['swap']=='0'
 b=subprocess.check_output(['git','show',j['source_revision']+':tools/pv-rdb2e-20261029/'+script]);j['input_script']=dict(path='tools/pv-rdb2e-20261029/'+script,sha256=hashlib.sha256(b).hexdigest(),source_revision=j['source_revision'])
 if name.startswith('native-associations'):j['evidence_class']='finite validation only; no universal native or restored-row credit'
 p.write_text(json.dumps(j,indent=2)+'\n');native.append(dict(name=name,**j,receipt=str(p.relative_to(E))))
assert not subprocess.check_output(['git','diff','--name-only','1a3cd3de26','--','crates','programs','design'],text=True).strip()
for p in P.glob('PV_RDB2E_*.lean'):
 s=re.sub(r'/--.*?-/|/-.*?-/','',p.read_text(),flags=re.S);s=re.sub(r'--[^\n]*','',s)
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by|axiom)\b',s),p
 assert not re.search(r'^import .*\bXR',s,re.M),p
assert not [str(p)for p in E.rglob('*')if p.is_file()and p.stat().st_size>20_000_000]
r=dict(branch='codex/pv-rdb2e-20261029',base='1a3cd3de26',worktree=str(R),host_dir='/home/dombarker/project-offloads/codex-pv-rdb2e-20261029/',restored=[],suspended=['V256','V257','V231'],native_behavior_findings=[],lean_budget=dict(used=len(rows),total=100,exit_zero=sum(x['exit']==0 for x in rows),exit_nonzero=sum(x['exit']!=0 for x in rows),final_independent_cohort_passes=sum(x['independent_cohort_credit']for x in rows)),native_budget=dict(used=len(native),total=60),kani=0,attempts=rows,native_scopes=native,statement_audit=62297,axioms_audit=62298,focused_replay=62299,axioms_named_declarations=len(plan['named_declarations']),new_theorems_audited=len(plan['theorems']),independent_model_objects=len(fp['objects']),external_objects=len(fp['external']),allowed_axioms=sorted(allowed),sampler_cohort_stop='sampler-cohort-stop.json',uncredited_drafts=[str(p.relative_to(E))for p in sorted((E/'unsubmitted').glob('*'))],endpoint_premises=dict(removed=0,added=0,changed=0),T=['entropy_law','entropy_kernel','observation'],composition_trust='reclassification within existing tool trust, never premise removal',stop='100 Lean attempts exhausted; no whole-row native source instance restored',next='Resolve R72 object-cohort mismatch and rebuild its affected closure before any sampler credit; prove original raw iterator/from_fn association at verifier calls. For SHA, native core/buffer/output association, outer software mutable iterator/copy, and pending SHA-NI law remain.')
(E/'combined-audit.json').write_text(json.dumps(r,indent=2)+'\n')
for row in r['suspended']:
 (E/(row+'.json')).write_text(json.dumps(dict(row=row,disposition='SUSPENDED',class_='B',evidence_class='partial source projections and finite validation only; no restored-row credit',blocker_file=row+'.md',statement_audit=62297,axioms_audit=62298,focused_replay=62299,endpoint_premises=r['endpoint_premises'],T=r['T'],composition_trust=r['composition_trust']),indent=2)+'\n')
print(json.dumps({k:r[k]for k in ['lean_budget','native_budget','new_theorems_audited','axioms_named_declarations','independent_model_objects']}))
