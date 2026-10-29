#!/usr/bin/env python3
"""Validate domain-only native windows; this never promotes NDT rows."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent
read=lambda p:json.loads(p.read_text())
kmx='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def check(n,positive,needle):
 a=f'NED_K{n:03d}';cfg=read(E/(a+'.json'));r=read(E/a/'receipt.json');log=(E/a/'stdout.log').read_text()
 assert r['kind']=='kani' and r['exit_status']==(0 if positive else 1)
 assert r['limits']==limits and int(r['swaps'])==0 and r['source_revision']
 assert cfg['env']['CARGO_NET_OFFLINE']=='true' and cfg['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert cfg['copy_patch_sha256']==kmx and '--harness-timeout' in cfg['native_command']
 graph=read(E/(a+'-graph-check.json'));assert graph['graph_matches_frozen'] and graph['exact_LPm_graph']
 assert read(E/(a+'-lock-check.json'))['unchanged']
 assert read(E/(a+'-source-check.json'))['errors']==[]
 assert 'Timeout' not in log and 'VERIFICATION:- '+('SUCCESSFUL' if positive else 'FAILED') in log
 match=re.search(r'\*\* (\d+) of (\d+) failed',log);assert match and int(match[1])==(0 if positive else 1)
 if positive:assert '** 2 of 2 cover properties satisfied' in log
 else:assert needle in log
 return dict(attempt=a,receipt=dict(path=str(E/a/'receipt.json'),sha256=sha(E/a/'receipt.json')),source_pinset=r['source_hashes']['NED_RUST_SHA256.json'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r['source_revision'],features=cfg['statement_features'],patch_sha256=r['source_hashes']['NED_call_windows.patch'])

rows=[]
for t in range(7):
 p=10+2*t;n=p+1
 if not (E/f'NED_K{n:03d}'/'receipt.json').exists():continue
 pos=check(p,True,'');neg=check(n,False,'in pool_v1::pair_forest_terminal::NED_windows::check')
 assert pos['patch_sha256']==neg['patch_sha256']==sha(E/'NED_call_windows.patch')
 assert pos['features']==neg['features'] and pos['source_pinset']==neg['source_pinset']
 rows.append(dict(window=t,positive=pos,negative=neg,status='DOMAIN-ONLY',composed_credit=False))
print(json.dumps(dict(windows=rows,scope='actual frozen caller prefixes and arguments only; no native Result/state/ordered-effects substitution',closed_composed_rows=[]),indent=1))
