from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent;R=E.parent.parent
obj=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
CAPS={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
LOCK='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
KMX=sha(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch')
def check(a,want):
 rc=obj(E/a/'receipt.json');cfg=obj(E/(a+'.json'));log=(E/a/'stdout.log').read_text()
 assert rc['kind']=='kani' and rc['exit_status']==want and rc['limits']==CAPS and int(rc['swaps'])==0
 assert rc['copy_patch_sha256']==KMX
 assert rc['env']['CARGO_NET_OFFLINE']=='true' and rc['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert ('VERIFICATION:- FAILED' if want else 'VERIFICATION:- SUCCESSFUL') in log
 assert 'timed out' not in log.lower()
 admission=obj(E/(a+'-admission.json'));assert admission['exit_status']==0 and admission['reservation']['allowed'] is True
 graph=obj(E/(a+'-graph-check.json'));assert graph['graph_matches_frozen'] and graph['exact_frozen_selected_graph']
 assert graph['resolved_features_all_crates']
 lock=obj(E/(a+'-lock-check.json'));assert lock['unchanged'] and lock['before']==lock['after']==LOCK
 assert not obj(E/(a+'-source-check.json'))['errors']
 for p,h in rc['source_hashes'].items():assert sha(E/a/'sources'/p)==h,(a,p)
 return rc

def cm():
 records=[check(f'NET_K{i:03}',int(i in [2,3,4,6])) for i in range(1,7)]
 assert all(r['source_hashes']==records[0]['source_hashes'] for r in records)
 assert all(obj(E/f'NET_K{i:03}-graph-check.json')['resolved_features_all_crates']==obj(E/'NET_K001-graph-check.json')['resolved_features_all_crates'] for i in range(1,7))
 code=(E/'NET_K001/sources/NET_src/crates/aspis-core/src/field/NET_inverse.rs').read_text()
 assert code==(E/'NET_inverse.rs.txt').read_text()
 assert not any(t in code for t in ['static mut','UnsafeCell','RefCell','Atomic','Option<fn','stub_verified','proof_for_contract'])
 assert 'KMX_copy_nonoverlapping' in code
 return dict(status='PARTIAL_NATIVE_LOG; NOT COMPOSED',positive='NET_K001',controls=['NET_K002','NET_K003','NET_K004'],copy_controls=['NET_K005','NET_K006'],matched_source_hashes=records[0]['source_hashes'],frozen_graph_verified_each_run=True,offline_lock_unchanged_each_run=True,new_composed_rows=0,remaining=obj(E/'NET_INVERSE_SOURCE.json')['positive']['remaining'])
if __name__=='__main__':
 out=cm();(E/'NET_NATIVE_STAGE.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(status=out['status'],native_runs=6,new_composed_rows=0)))
