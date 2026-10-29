"""Validate fresh frozen native bindings, caller control, decoder windows."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent
read=lambda p:json.loads(p.read_text())
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
def receipt(n,positive,covers):
 a=f'NED_K{n:03d}';r=read(E/a/'receipt.json');cfg=read(E/(a+'.json'));log=(E/a/'stdout.log').read_text()
 assert r['exit_status']==int(not positive) and r['limits']==limits and int(r['swaps'])==0
 assert cfg['env']['CARGO_NET_OFFLINE']=='true' and cfg['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert cfg['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 assert read(E/(a+'-graph-check.json'))['exact_LPm_graph'] and read(E/(a+'-graph-check.json'))['graph_matches_frozen']
 assert read(E/(a+'-lock-check.json'))['unchanged'] and read(E/(a+'-source-check.json'))['errors']==[]
 failed=re.search(r'\*\* (\d+) of (\d+) failed',log);assert failed and int(failed[1])==int(not positive)
 assert ('VERIFICATION:- SUCCESSFUL' if positive else 'VERIFICATION:- FAILED') in log
 if positive:assert f'** {covers} of {covers} cover properties satisfied' in log
 else:assert 'in pool_v1::pair_forest_terminal::NED_' in log and 'Failed Checks:' in log
 return dict(attempt=a,receipt=f'evidence/slice-s-compose-20261029/{a}/receipt.json',sha256=hashlib.sha256((E/a/'receipt.json').read_bytes()).hexdigest(),source_pinset=r['source_hashes']['NED_RUST_SHA256.json'],features=cfg['statement_features'])
rows=[]
for n,label,covers in [(24,'public tuple, all six coordinates',2),(26,'M31 raw serialization',1),(28,'original common pointer',2),(30,'statement variant kind',2),(32,'payment variant kind',2),(34,'actual validator abstract Result and ordered call log',4),(36,'request payment payload slice',2),(38,'statement payment payload and earlier Box pointer',2)]:
 p=receipt(n,True,covers);q=receipt(n+1,False,covers);assert p['source_pinset']==q['source_pinset'] and p['features']==q['features']
 rows.append(dict(subject=label,positive=p,negative=q))
pointer_only=receipt(40,True,2)
print(json.dumps(dict(address_only_unpaired=pointer_only,pairs=rows,composed_rows_closed=[],scope='bindings/control/domain evidence; native child value, physical and effect obligations retained'),indent=1))
