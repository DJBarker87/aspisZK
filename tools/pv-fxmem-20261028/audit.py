"""Compile-free final scope, receipt and source audit; never launches a compiler."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-fxmem-20261028';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
assert str(R)=='/Users/dominic/ZK/.worktrees/pv-fxmem'
git=lambda *a:subprocess.check_output(['git',*a],cwd=R,text=True).strip()
assert git('branch','--show-current')=='codex/pv-fxmem-20261028'
subprocess.run(['git','merge-base','--is-ancestor','7e46a8b2c9','HEAD'],cwd=R,check=True)
changed=git('diff','--name-only','7e46a8b2c9..HEAD').splitlines()
allowed=('evidence/pv-fxmem-20261028/','tools/pv-fxmem-20261028/','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_FXM_')
assert all(p.startswith(allowed) for p in changed),changed
assert not git('status','--porcelain','--','crates','programs')
sha=lambda b:hashlib.sha256(b).hexdigest()
runs=[]
for p in sorted(E.glob('355*.json')):
 if not re.fullmatch(r'355\d\d',p.stem):continue
 j=json.loads(p.read_text());n=int(p.stem)
 assert j['id']==n and 35500<=n<=35599
 src=E/f'{n}-source.lean.txt';assert sha(src.read_bytes())==j['source_sha256'],n
 path=j.get('source_path','docs/research/v8-r0-zk-20261009/lean/'+j['module']+'.lean')
 pinned=subprocess.check_output(['git','show',j['source_revision']+':'+path],cwd=R)
 assert sha(pinned)==j['source_sha256'],('revision mismatch',n)
 for key in ['exit','wall','peak_rss_kib','swap','source_revision']:assert j.get(key) is not None,(n,key)
 assert str(j['swap'])=='0',n
 assert int(j['peak_rss_kib'])<8*1024*1024,n
 if j.get('accepted'):
  expected=len(re.findall(r'^#print axioms ',src.read_text(),re.M))
  assert len(j.get('axioms',[]))==expected,(n,expected,len(j.get('axioms',[])))
  for a in j['axioms']:
   m=re.search(r'depends on axioms: \[([^\]]*)\]',a)
   if m:assert set(x.strip() for x in m[1].split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'},(n,a)
 runs.append(j)
assert len({j['id'] for j in runs})==len(runs)
modules=[]
for p in sorted(L.glob('PV_FXM_*.lean')):
 s=p.read_text();b=p.read_bytes();module='R1Z/'+p.stem
 code=re.sub(r'/\-.*?\-/|--[^\n]*','',s,flags=re.S)
 assert not re.search(r'\b(sorry|admit|native_decide)\b',code),p
 assert not re.search(r'^\s*(axiom|opaque|constant)\s',code,re.M),p
 assert 'set_option max' not in code,p
 names=re.findall(r'^(?:theorem|lemma)\s+(\w+)',code,re.M)
 queries=re.findall(r'^#print axioms (\S+)',s,re.M)
 for n in names:assert n in queries,(p,n)
 matches=[j for j in runs if j['module']==module and j['source_sha256']==sha(b) and j.get('accepted')]
 assert matches,('no accepted current-source compile',module)
 j=matches[-1]
 modules.append(dict(module=module,path=str(p.relative_to(R)),sha256=sha(b),blob=git('rev-parse','HEAD:'+str(p.relative_to(R))),accepted_attempt=j['id'],theorems=names,queries=queries))
for n in [35597,35598,35599]:assert any(j['id']==n and j.get('accepted') for j in runs)
assert len(next(j for j in runs if j['id']==35598)['axioms'])==79
manifest=dict(source_revision=git('rev-parse','HEAD'),modules=modules,external_authority=dict(path='external-object-manifest.json',sha256=sha((E/'external-object-manifest.json').read_bytes()),count=5673),source_gates={p.name:sha(p.read_bytes()) for p in E.glob('STRUCTURAL-*-GATE.json')},scope='Source packages and focused callback closure only; no endpoint removal or deployed binary claim',ok=True)
(E/'FINAL-SOURCE-MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
summary=[]
for j in runs:
 summary.append({k:j.get(k) for k in ['id','module','source_revision','source_sha256','exit','wall','peak_rss_kib','swap','accepted']})
(E/'ATTEMPTS.json').write_text(json.dumps(summary,indent=2)+'\n')
t=json.loads((E/'TALLY.json').read_text());t.update(lean_charged=len(runs),lean_accepted=sum(bool(j.get('accepted')) for j in runs),lean_rejected=sum(not j.get('accepted') for j in runs),used_ids=[j['id'] for j in runs],lean_unspent=100-len(runs),lean_resume_budget=98,lean_resume_charged=len(runs)-2,kani_used=0,audit_ids_unused=[],source_scope_packages_complete=['V170 finite Vec<u32>','V183 allocator-world family','V221 emitted byte-array dictionaries','V222 emitted primitive-byte dictionary'],closed_rows=[],ledger_rows_changed=[],endpoint_premises_removed=0,target_established=False,native_finite_paired_cases=4756,native_scalar_cases=1280,stop_reason='All four explicitly scoped structural source packages complete; combined installation, 79-query axioms audit and one focused closure replay pass. Lead recount/endpoint and L3 realization remain open.')
t.pop('native_finite_checks',None)
t['retained_finding_native_pairs']=32
t['audit_ids_used']=[35597,35598,35599]
t['unused_ids']=[n for n in range(35500,35600) if n not in t['used_ids']]
(E/'TALLY.json').write_text(json.dumps(t,indent=2)+'\n')
md=['# Numbered compiler receipts','', '| ID | Module | Exit | Wall | Peak RSS KiB | Swap | Source revision | Credit |','|---|---|---:|---:|---:|---:|---|---|']
for j in runs:
 md.append(f"| {j['id']} | {j['module'].split('/')[-1]} | {j['exit']} | {j['wall']} | {j['peak_rss_kib']} | {j['swap']} | {j['source_revision'][:10]} | {'accepted' if j.get('accepted') else 'rejected'} |")
md+=['','Full target command, source blob/hash, dependency fingerprint, environment and raw #print axioms are in each numbered JSON and output log (private logs under lean-ID/). The inherited error type module has no added theorem; its axiom query count is zero. Refusals consume no compile attempts. No unchanged submitted compiler was rerun for receipt recovery.','', '35516 and 35518 are charged own-environment failures, corrected with changed output/import environments under rule 11. COOLDOWN-DEVIATION.json records one early retry; no cap or admission was bypassed. Legacy attempts 35500/35501 retain their accepted standing TasksMax=128 record; the observed current shared launcher and every private/native scope use TasksMax=64.']
(E/'RECEIPTS.md').write_text('\n'.join(md)+'\n')
large=[str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024];assert not large,large
print(json.dumps(dict(ok=True,modules=len(modules),charged=len(runs),accepted=t['lean_accepted'],rejected=t['lean_rejected'],remaining=t['lean_unspent'],resume_charged=t['lean_resume_charged'],max_rss_kib=max(int(j['peak_rss_kib']) for j in runs))))
