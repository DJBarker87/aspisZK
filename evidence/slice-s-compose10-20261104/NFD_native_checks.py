from pathlib import Path
from NFD_validate import E,R,read,sha
import re,json
def native(a,positive):
 r=read(E/a/'receipt.json');c=read(E/(a+'.json'))
 assert r['kind']=='kani' and r['source_revision'] and int(r['swaps'])==0
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert c['env']['CARGO_NET_OFFLINE']=='true' and c['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert c['native_command'][0]=='/home/dombarker/.cargo/bin/cargo-kani'
 assert '--locked' not in c['native_command'] and c['native_command'][c['native_command'].index('--harness-timeout')+1]=='90s'
 assert r['exit_status']==(0 if positive else 1)
 assert all(r[k]==v for k,v in c.items())
 ad=read(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert read(E/(a+'-graph-check.json'))['exact_LPm_graph'] is True
 from NFD_frozen_identity import check as frozen_identity
 assert read(E/(a+'-frozen-identity.json'))==frozen_identity(a)
 assert read(E/(a+'-lock-check.json'))['unchanged'] is True
 assert read(E/(a+'-rule16-check.json'))['no_writable_static'] is True
 assert not read(E/(a+'-source-check.json'))['errors']
 assert c['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 log=(E/a/'stdout.log').read_text()
 assert ('VERIFICATION:- SUCCESSFUL' in log) is positive
 assert positive or 'Failed Checks:' in log
 assert 'timed out' not in log.lower()
 archive=E/(a+'-inputs.json')
 snapshots=read(archive)[a] if Path(str(archive)+'.xz').exists() else read(E/'NFD_SOURCE_HISTORY.json')[a]
 assert set(snapshots)==set(r['source_hashes'])
 assert all(sha(s.encode())==r['source_hashes'][n] for n,s in snapshots.items())
 for n in ['NFD_native_contracts.patch','NFD_oracle.patch']:assert snapshots[n]==(E/(a+'-'+n)).read_text()
 source=snapshots['NFD_native_contracts.patch']
 assert not any(s in source.replace('AtomicStatementError','') for s in ['static mut','stub_verified','UnsafeCell','Atomic','transmute'])
 assert not re.search(r'\bstatic\s+mut\b|\b(?:Cell|RefCell|UnsafeCell)\b',source)
 features={p['name']:set(p['features']) for p in read(E/(a+'-metadata-pin.json'))['features_all_crates']}
 assert set(c['required_statement_features'])<=features['aspis-statement']
 if 'program_features' in c:
  assert {'pool-adapter','private-leaf-salts'}<=features['aspis-r1-cost-probe-program']
  assert not {'no-entrypoint','cu-profiling'}&features['aspis-r1-cost-probe-program']
  assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=features['aspis-r1-cost-probe']
 return snapshots
