"""Aggregate the single full raw walk; never infer native row closure."""
from pathlib import Path
import json,hashlib,lzma
B=Path.cwd();plan=json.loads((B/'NMB_AUDIT_ROOTS.json').read_text());results=[];groups=[];nonzero=[]
for i,names in enumerate(plan['groups']):
 p=B/'NMB_audit'/('proof'+str(i))/('proof'+str(i)+'.json');r=json.loads(p.read_text());assert{v['root']for v in r['results']}==set(names);results+=r['results'];groups.append({k:r[k]for k in ['target','exit_status','wall_seconds','peak_rss_kib','swaps']})
 if r['exit_status']:
  assert r['exit_status']==1 and any(not v['equal']for v in r['results']),'Unclassified nonzero audit exit'
  nonzero.append(dict(group=i,exit_status=r['exit_status']))
assert len(results)==len(plan['roots'])and{r['root']for r in results}==set(plan['roots'])
standard={'propext','Classical.choice','Quot.sound'};assert all(set(r['walked_axioms'])<=standard for r in results)
fixtures=json.loads((B/'NMB_audit/fixtures/fixtures.json').read_text());assert len(fixtures['results'])==8 and all(r['equal']for r in fixtures['results'])
scan=[json.loads(l)for l in(B/'NMB_LOADED_scan.jsonl').read_text().splitlines()];assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
receipts=[json.loads(p.read_text())for p in B.glob('NMB_[LK][0-9][0-9][0-9]/receipt.json')];assert all(r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}for r in receipts)
exe={}
for r in receipts:
 for n,p in r.get('deps_fingerprint',{}).get('executables',{}).items():
  assert n not in exe or exe[n]==p['sha256'];exe[n]=p['sha256']
x=dict(status='PASS_FULL_CACHED_SOURCE_GATE_WITH_RETAINED_COLLECTOR_FINDINGS',headline='AspisR1.RPx_Deployed.deployed',required_roots=len(results),all_required_raw_roots_present=True,raw_standard_axioms_only=True,axioms=sorted(set(a for r in results for a in r['walked_axioms'])),collect_axioms_disagreements=[r for r in results if not r['equal']],retained_nonzero_audit_exits=nonzero,groups=groups,fixtures=fixtures['results'],scanner=dict(modules=len(scan),dangling=0,duplicate_owners=0,import_mismatches=0,compatible_replicas=sum(len(r.get('cached_replicas',[]))for r in scan)),raw_authoritative_ruling="(ab')(3)/(ax2)",audit_executable_sha256=exe,cold_release_replay=False,source_gate_pass=True,native_parent_composition=False,row_roots=[],row_promotions=0,security_target_established=False,baseline='ledger23 NLO580 CLOSED/0 QUALIFIED/19 OPEN',production_audit_count=1)
(B/'NMB_AUDIT.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(dict(roots=len(results),groups=len(groups),collector_disagreements=len(x['collect_axioms_disagreements']),target_established=False)))
