"""One final artifact/policy audit; invokes no compiler, solver or manifest replay."""
from pathlib import Path
import json,lzma,hashlib,re,subprocess,sys
E=Path(__file__).resolve().parent;root=E.parents[1]
assert str(root)=='/Users/dominic/ZK/.worktrees/pv-k3scan'
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/pv-k3scan-20261101'
s=json.loads((E/'D549-RESULTS.json').read_text());assert s['charged_invocations']==60 and not s['campaign_in_progress'];rs=s['results'];assert len({r['id']for r in rs})==60 and all(re.fullmatch(r'K792[0-9]{2}',r['id'])for r in rs)
assert 'K79230'not in {r['id']for r in rs}
assert s['counts']=={'PASS':29,'EXPECTED_CONTROL_FAIL':29,'SETUP_FAILURE':2},s['counts']
assert [r['id']for r in rs if r['result']=='SETUP_FAILURE']==['K79208','K79219']
assert len(s['pairs'])==29 and s['Lean']==0 and s['endpoint_premises_removed_added_weakened']==[0,0,0]
by={r['id']:r for r in rs};checks=[]
for pair in s['pairs']:
 p,n=pair['positive'],pair['control'];a=by[p];b=by[n];assert a['result']=='PASS' and b['result']=='EXPECTED_CONTROL_FAIL';assert a['failed_checks']==0 and b['failed_checks']==1
 ah=json.loads((E/'host'/p/'source-sha256.json').read_text());bh=json.loads((E/'host'/n/'source-sha256.json').read_text());assert ah==bh,(p,n,'source inventories differ')
 if pair['credit_ids']!=['C044']:
  aa=a['config'];bb=b['config'];assert aa['package']==bb['package'];assert aa.get('stubs',[])==bb.get('stubs',[]);assert aa.get('kani_extra',[])==bb.get('kani_extra',[])
  assert bb['harness'] in [aa['harness'],aa['harness']+'_wrong'];assert bb['negative'] and not aa['negative']
 text=(E/'host'/n/'output.log').read_text();assert 'unwinding assertion'not in text.lower();assert 'Failed Checks: assertion failed:'in text or ('Failed Checks: This is a placeholder message;'in text and 'in core::panicking::assert_failed_inner'in text),n
 checks.append({'positive':p,'control':n,'source_hashes_equal':True,'control_failed_checks':1,'source_local_or_typed_assertion_panic':True})
for r in rs:
 assert r['swap']==0 and r['peak_rss_kib'] is not None and r['wall_seconds']>0
 assert r['print_axioms']=='N/A: Kani; 0 Lean';assert r['resolved_revision']
 a=json.loads((E/'host'/r['id']/'admission.json').read_text());b=json.loads((E/'host'/r['id']/'barrier.json').read_text());assert a['allowed'] and b['allowed'];assert b['own_limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for a,b in zip(rs,rs[1:]):assert b['epoch']-a['epoch']>=180,(a['id'],b['id'])
pre=E/'host/K79206-preflight';assert (pre/'metadata.stderr').exists() and not (pre/'STARTED.json').exists()
c=json.loads(lzma.decompress((E/'CREDITS.json.xz').read_bytes()));assert len(c)==305 and len({x['credit_id']for x in c})==305
assert hashlib.sha256(lzma.decompress((E/'CREDITS.json.xz').read_bytes())).hexdigest()==(E/'CREDITS.json.sha256').read_text().strip()
for cid in ['C051','C053','C156','C163','C164']:assert next(x for x in c if x['credit_id']==cid)['final_status']=='SUSPENDED'
for cid in ['C042','C155','C157','C088','C089']:assert next(x for x in c if x['credit_id']==cid)['final_status']=='RESTORED'
rows=json.loads((E/'K3-ROWS.json').read_text());assert not rows['campaign_in_progress'];assert len(rows['rows'])==34
for row in rows['rows']:
 bad=[cid for cid in row['current_kani_support']if next(x for x in c if x['credit_id']==cid)['final_status']=='SUSPENDED'];assert row['depends_on_still_suspended_credit']==bool(bad)
assert sum(x['depends_on_still_suspended_credit']for x in rows['rows'])==0
# The audit's payloads are source/data snapshots, not compiled objects or executables.
for p in E.glob('*.json.sha256'):
 q=E/(p.name.removesuffix('.sha256')+'.xz')
 if q.exists():assert hashlib.sha256(lzma.decompress(q.read_bytes())).hexdigest()==p.read_text().strip(),str(q)
for p in E.rglob('*'):
 if p.is_file() and 'v185-source'not in p.parts:assert p.stat().st_size<=20*1024*1024,str(p)
changed=subprocess.check_output(['git','diff','--name-only','bad175c553','--'],text=True).splitlines();assert all(n.startswith('evidence/pv-k3scan-20261101/')for n in changed),changed
out={'status':'PASS','scope':'Final D549 source/receipt/pair/resource/current-row audit; no compiler or solver invocation','charged_invocations':60,'pairs':checks,'setup_failures':['K79208','K79219'],'metadata_preflight_uncharged':'K79206-preflight','all_swaps':0,'max_peak_rss_kib':max(r['peak_rss_kib']for r in rs),'wall_seconds_sum':sum(r['wall_seconds']for r in rs),'minimum_launch_gap_seconds':min(b['epoch']-a['epoch']for a,b in zip(rs,rs[1:])),'credit_status':s['credit_status'],'rows':34,'current_scopes_depending_on_suspended_credit':0,'Lean':0,'axioms':'N/A: Kani; 0 Lean','endpoint_premises_removed_added_weakened':[0,0,0]}
(E/'D549-VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='pairs'}))
