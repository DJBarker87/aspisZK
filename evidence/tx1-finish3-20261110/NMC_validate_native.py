"""Strict read-only review of every native verdict and its frozen configuration."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;rows=[]
for n in range(1,41):
 a=f'NMC_K{n:03}';p=E/a/'receipt.json';assert p.exists(),a
 x=json.loads(p.read_text());cfg=json.loads((E/(a+'.json')).read_text());log=(p.parent/'stdout.log').read_text()
 graph=json.loads((E/(a+'-graph-check.json')).read_text());lock=json.loads((E/(a+'-lock-check.json')).read_text())
 admission=json.loads((E/(a+'-admission.json')).read_text());assert admission['exit']==0 and admission['reservation']['allowed']is True
 assert graph['graph_matches_frozen']and lock['unchanged']
 for suffix in ['-source-check.json','-baseline-check.json']:assert not json.loads((E/(a+suffix)).read_text())['errors']
 assert cfg['env']['CARGO_NET_OFFLINE']=='true'and cfg['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert 'pool-adapter,private-leaf-salts'in cfg['native_command']
 selected=next(r for r in graph['selected_closure']if r['name']=='aspis-r1-cost-probe')
 assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=set(selected['features'])
 pins=json.loads((p.parent/'sources/NMC_SOURCE_PINS.json').read_text());assert pins['KMX_stubs.rs']=='ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138'
 timeout='timed out'in log or x['exit_status']==124
 bad=cfg['module'].endswith('_control')
 semantic_fail=(x['exit_status']==1 and 'Failed Checks: assertion failed: !ok'in log and not timeout)
 passed=x['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL'in log
 status='TIMEOUT_NO_CREDIT'if timeout else 'MATCHED_ASSERTION_FAIL'if bad and semantic_fail else'PASS_WINDOW'if passed else'FINDING'
 assert status!='FINDING',(a,status)
 rows.append(dict(attempt=a,harness=cfg['module'],status=status,exit_status=x['exit_status'],wall_seconds=x['wall_seconds'],peak_rss_kib=x['peak_rss_kib'],swaps=x['swaps'],source_pins_sha256=hashlib.sha256((p.parent/'sources/NMC_SOURCE_PINS.json').read_bytes()).hexdigest(),frozen_graph=True,lock_unchanged=True,deployed_features=True,copy_mitigation=True))
pairs=[(3,4)]+[(n,n+1)for n in range(5,21,2)]+[(n,n+1)for n in range(22,38,2)]
for a,b in pairs:
 assert rows[a-1]['status']=='PASS_WINDOW'and rows[b-1]['status']=='MATCHED_ASSERTION_FAIL'
 assert rows[a-1]['source_pins_sha256']==rows[b-1]['source_pins_sha256']
out=dict(status='PASS_PARTIAL_WINDOW_REVIEW_ONLY',kani_used=40,paired_windows=len(pairs),timeouts=[r['attempt']for r in rows if r['status']=='TIMEOUT_NO_CREDIT'],unpaired_positive=['NMC_K038'],full_segments_closed=[],row136='OPEN',process_findings=['K040 inverted the assertion on K039 same full-entry footprint after timeout; this did not isolate the shape and earns no replacement/control credit'],rows=rows)
(E/'NMC_NATIVE_REVIEW.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items()if k!='rows'}))
