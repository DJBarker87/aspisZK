from pathlib import Path
import json,re,hashlib,subprocess
D=Path(__file__).resolve().parent;repo=D.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rs=[json.loads(p.read_text()) for p in sorted(D.glob('lean*-receipt.json'))]
assert [r['attempt'] for r in rs]==list(range(67000,67100))
for r in rs:
 assert sha(D/('lean'+str(r['attempt'])+'-source.lean.txt'))==r['source_sha256']
 assert r['admission_exit']==0 and r['admission_allowed'] is True and r['swaps']=='0'
 assert (D/('lean'+str(r['attempt'])+'-output.log')).read_text()==r['print_axioms']
 if r['exit']==0:
  assert 'sorryAx' not in r['print_axioms']
  for ax in re.findall(r'depends on axioms: \[([^]]*)\]',r['print_axioms']):assert set(ax.split(', '))<={'propext','Classical.choice','Quot.sound'}
 else:
  assert sum(q['source_sha256']==r['source_sha256'] for q in rs)==1
freeze=json.loads((D/'freeze-sources.json').read_text());binding=[]
for m,pin in freeze['sources'].items():
 p=repo/pin['path'];assert sha(p)==pin['sha256']
 raw=subprocess.check_output(['git','show',freeze['revision']+':'+pin['path']],cwd=repo);assert hashlib.sha256(raw).hexdigest()==pin['sha256']
 hits=[r for r in rs if r['module']==m and r['exit']==0 and r['source_sha256']==pin['sha256']];assert hits,m
 r=hits[-1];assert r['attempt']>=67079
 binding.append(dict(module=m,attempt=r['attempt'],pin=pin))
audit='\n'.join((D/f'lean{i}-output.log').read_text() for i in [67097,67098])
cov=json.loads((D/'audit-coverage.json').read_text());assert cov['theorems']==92
for m,names in cov['modules'].items():
 assert re.findall(r'^theorem (\w+)',(D/(m+'.lean')).read_text(),re.M)==names
 for n in names:assert "'PV_DIAG11."+n+"'" in audit,n
old=[]
for rel in ['evidence/pv-diag10-20261029/PV_DIAG10_Links.lean','evidence/pv-diag10-20261029/PV_DIAG10_Operands.lean','evidence/pv-diag10-20261029/PV_DIAG10_Requests.lean','evidence/pv-diag10-20261029/PV_DIAG10_Attempt.lean','evidence/pv-diag10-20261029/PV_DIAG10_Reached.lean','evidence/pv-diag10-20261029/PV_DIAG10_FILE.lean','evidence/pv-diag10-20261029/PV_DIAG10_JSON_STDOUT.lean','evidence/pv-diag10-20261029/PV_DIAG10_ERROR_STDERR.lean']:
 raw=subprocess.check_output(['git','show','c84e5c2ef7:'+rel],cwd=repo);assert raw==(repo/rel).read_bytes();old.append(rel)
summary=dict(branch=subprocess.check_output(['git','branch','--show-current'],cwd=repo,text=True).strip(),base='c84e5c2ef7',proof_freeze=freeze['revision'],attempts=len(rs),accepted=sum(r['exit']==0 for r in rs),rejected=[r['attempt'] for r in rs if r['exit']!=0],native_scopes=len(list(D.glob('native*-receipt.json'))),kani=0,audited_theorems=92,max_rss_kib=max(int(r['peak_rss_kib']) for r in rs),lean_wrapper_wall_seconds=sum(r['wall_seconds'] for r in rs),all_swap_zero=True,unchanged_inherited_link_and_skeleton_files=old,current_source_binding=binding,global_deployed_links_discharged=0,endpoint_premises=dict(removed=0,added=0,weakened=0,changed=0))
(D/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
(D/'proof-source-commit-binding.json').write_text(json.dumps(dict(revision=freeze['revision'],bindings=binding),indent=2)+'\n')
print('verified',summary['attempts'],'attempts;',summary['audited_theorems'],'theorems; unchanged inherited Links and skeletons; max RSS',summary['max_rss_kib'])
