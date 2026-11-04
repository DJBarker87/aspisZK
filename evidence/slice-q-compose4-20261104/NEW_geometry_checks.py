"""Partial native packet admission. It never promotes a composed row."""
from NEW_inverse_checks import *
KMX=sha(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch')
def native(a,want):
 r=receipt(a,want)
 assert r['env'].get('CARGO_NET_OFFLINE')=='true',(a,'offline environment absent')
 assert '-O0' not in r['env'].get('RUSTFLAGS','')
 assert r['env'].get('CARGO_PROFILE_DEV_OPT_LEVEL')=='3'
 assert obj(E/(a+'.json'))['copy_patch_sha256']==KMX
 graph=obj(E/(a+'-graph-check.json'));assert graph['graph_matches_frozen'] and graph['exact_frozen_selected_graph']
 lock=obj(E/(a+'-lock-check.json'));assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 log=(E/a/'stdout.log').read_text()
 assert ('VERIFICATION:- SUCCESSFUL' if want==0 else 'VERIFICATION:- FAILED') in log
 assert not any(t in log for t in ['TIMEOUT','internal compiler error','timed out','SIGKILL'])
 inputs=json.loads(lzma.decompress((E/(a+'_INPUTS.json.xz')).read_bytes()))
 assert hashlib.sha256(inputs['NEW_src/KMX_stubs.rs'].encode()).hexdigest()=='ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138'
 assert inputs['NEW_gate.py'].startswith('"""Own strict validation')
 assert "os.environ.get('CARGO_NET_OFFLINE')=='true'"in inputs['NEW_gate.py']
 return dict(attempt=a,exit=want,wall=r['wall_seconds'],rss=r['peak_rss_kib'],swaps=r['swaps'],source_hashes=r['source_hashes'],patch_sha256=KMX,composed_credit=False)
def pair(a,*bad):
 good=native(a,0);controls=[native(x,1)for x in bad]
 for c in controls:assert good['source_hashes']==c['source_hashes'],'different configuration sources'
 return dict(positive=good,controls=controls,composed_credit=False)
if __name__=='__main__':print(json.dumps(pair(*sys.argv[1:]),indent=1))
