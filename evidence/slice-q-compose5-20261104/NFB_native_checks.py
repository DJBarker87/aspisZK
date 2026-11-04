"""Admit exact native receipts; failed compilation/timeout is never a control."""
from pathlib import Path
import json,hashlib,lzma
E=Path(__file__).resolve().parent
obj=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
LOCK='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
LIMITS={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
def native(a,want,read=obj):
 r=read(E/a/'receipt.json');cfg=read(E/(a+'.json'));ad=read(E/(a+'-admission.json'))
 assert r['kind']=='kani' and r['exit_status']==want
 assert r['limits']==LIMITS and int(r['swaps'])==0
 assert float(r['wall_seconds'])>0 and int(r['peak_rss_kib'])>0
 assert ad['exit_status']==0 and ad['reservation']['allowed'] is True
 assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert '--locked' not in cfg['native_command']
 assert cfg['native_command'][cfg['native_command'].index('--features')+1]=='private-leaf-salts,optimized-terminal,program-build'
 graph=read(E/(a+'-graph-check.json'))
 assert graph['graph_matches_frozen'] is True and graph['exact_frozen_selected_graph'] is True
 assert graph['lock_sha256']==LOCK and graph['resolved_features_all_crates']
 features={p['name']:p['features'] for p in graph['selected_closure']}
 assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=set(features['aspis-r1-cost-probe'])
 assert {'r0','pool-v1-kernel'}<=set(features['aspis-statement'])
 lock=read(E/(a+'-lock-check.json'));assert lock['unchanged'] and lock['before']==lock['after']==LOCK
 assert not read(E/(a+'-source-check.json'))['errors']
 assert cfg['copy_patch_sha256']==sha(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch')
 log=(E/a/'stdout.log').read_text()
 assert ('VERIFICATION:- SUCCESSFUL' if want==0 else 'VERIFICATION:- FAILED') in log
 if want:assert 'Failed Checks:' in log
 assert not any(s in log.lower() for s in ['timed out','timeout','internal compiler error','could not compile','sigkill'])
 data=lzma.decompress((E/(a+'_INPUTS.json.xz')).read_bytes())
 assert hashlib.sha256(data).hexdigest()==(E/(a+'_INPUTS.json.sha256')).read_text().strip()
 inputs=json.loads(data);assert set(inputs)==set(r['source_hashes'])
 for name,source in inputs.items():assert hashlib.sha256(source.encode()).hexdigest()==r['source_hashes'][name]
 assert inputs['NFB_src/Cargo.lock'] and r['source_hashes']['NFB_src/Cargo.lock']==LOCK
 assert r['source_hashes']['NFB_src/KMX_stubs.rs']=='ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138'
 native_source=inputs['NFB_src/crates/aspis-r1-cost-probe/src/verifier/NFB_geometry.rs']
 for text in ['static mut','UnsafeCell','RefCell','Atomic','Option<fn','proof_for_contract','stub_verified']:
  assert text not in native_source
 return dict(attempt=a,target=r['target'],source_hashes=r['source_hashes'],exit=want,wall=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],print_axioms='N/A: native Kani check',quarantined=False,suspended=False)
def pair(good,*bad,read=obj):
 p=native(good,0,read);neg=[native(a,1,read) for a in bad]
 assert neg
 for n in neg:assert n['source_hashes']==p['source_hashes'],'configuration source drift'
 return dict(positive=p,controls=neg)
def copy_group(good,bad,targets,read=obj):
 c=pair(good,bad,read=read)
 assert c['positive']['target'].endswith('KMX_checks::KMX_ptr_correct')
 assert c['controls'][0]['target'].endswith('KMX_checks::KMX_ptr_wrong')
 for a in targets:
  p=native(a,0,read);assert p['source_hashes']==c['positive']['source_hashes'],'copy control configuration mismatch'
 return dict(copy_control=c,targets=targets)
