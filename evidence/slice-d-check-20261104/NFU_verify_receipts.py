"""Final receipt/feature/budget checks; no prover invocation or added credit."""
from pathlib import Path
import json,hashlib,collections,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1]
J=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts={p.parent.name:J(p)for p in E.glob('NFU_*/receipt.json')}
assert {a for a in receipts if a.startswith('NFU_K')}=={f'NFU_K{i:03}'for i in range(1,101)}
assert {a for a in receipts if a.startswith('NFU_L')}=={f'NFU_L{i:03}'for i in range(1,61)}-{'NFU_L047'}
assert {a for a in receipts if a.startswith('NFU_E')}=={f'NFU_E{i:03}'for i in range(1,4)}
assert (E/'NFU_L047-queue.log').exists() and not (E/'NFU_L047/receipt.json').exists()
entries=[json.loads(line)for line in (E/'NFU_ATTEMPTS.jsonl').read_text().splitlines()if line.strip()]
assert len(entries)==len(receipts)+1 and len({x['attempt']for x in entries})==len(entries)
assert {x['attempt']for x in entries}==set(receipts)|{'NFU_L047'}
assert next(x for x in entries if x['attempt']=='NFU_L047')['launched'] is False
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
features=[]
for a,rc in receipts.items():
 ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert rc['limits']==limits and int(rc['swaps'])==0
 for field in ['module','exit_status','wall_seconds','peak_rss_kib','source_revision','source_hashes','deps_fingerprint','print_axioms']:assert field in rc
 for n,h in rc['source_hashes'].items():
  p=E/a/'sources'/n
  if p.exists():assert sha(p)==h,(a,n)
 if rc['kind']!='kani':continue
 g=J(E/(a+'-graph-check.json'));l=J(E/(a+'-lock-check.json'));assert g['graph_matches_frozen'] and l['unchanged'] and l['before']==l['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 assert not J(E/(a+'-source-check.json'))['errors']
 assert rc['env']['CARGO_NET_OFFLINE']=='true' and rc['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert '--locked'not in rc['native_command']
 baseline='NFQ_K019'if rc.get('root_package')=='aspis-r1-cost-probe-program'else 'NFQ_K002' if 'root_package'in rc else 'NFQ_K002'
 bg=J(R/'evidence/slice-d-define-20261104'/(baseline+'-graph-check.json'))
 assert g['selected_closure']==bg['selected_closure'],a
 features.append(dict(attempt=a,baseline=baseline,selected_closure_exact=True,graph_sha256=g['graph_sha256']))
# Every completed finish observation and metadata packet has an exact same-name failing control.
pairs=[(72,73),(74,75),(76,77)]+[(i,i+1)for i in range(79,99,2)]+[(99,100)]
for p,n in pairs:
 pa,na=[receipts[f'NFU_K{i:03}']for i in [p,n]];assert pa['exit_status']==0 and na['exit_status']==1 and pa['module']==na['module']
 for i,result in [(p,'SUCCESSFUL'),(n,'FAILED')]:assert 'VERIFICATION:- '+result in (E/f'NFU_K{i:03}'/'stdout.log').read_text()
 assert pa['source_hashes']==na['source_hashes']
# No shipped-source or inventory mutation. Only own evidence is in this branch's delta.
worker_base=subprocess.check_output(['git','rev-parse','3879c16c0d8^'],cwd=R,text=True).strip();assert worker_base.startswith('f87d767e34e')
paths=subprocess.check_output(['git','diff','--name-only',worker_base],cwd=R,text=True).splitlines()
assert all(p.startswith('evidence/slice-d-check-20261104/')for p in paths),[p for p in paths if not p.startswith('evidence/slice-d-check-20261104/')]
large=[str(p.relative_to(E))for p in E.rglob('*')if p.is_file()and p.stat().st_size>20_000_000];assert not large,large
report=dict(status='PASS',charged_budget=dict(kani=100,lean_support=60,extraction=3),actual_capped_scopes=dict(kani=100,lean_support=59,extraction=3),prelaunch_charged='NFU_L047: own missing transitive dependency; no launch, repaired/split; counted conservatively',worker_base=worker_base,receipt_count=len(receipts),all_swaps_zero=True,all_caps_exact=True,all_admissions_allowed_and_exit0=True,source_snapshots_match=True,shipping_and_inventory_unchanged=True,feature_parity=features,finish_and_metadata_pairs=pairs,no_extra_closure_credit=True)
(E/'NFU_RECEIPTS_CHECK.json').write_text(json.dumps(report,indent=1)+'\n')
print(json.dumps({k:v for k,v in report.items()if k!='feature_parity'}))
