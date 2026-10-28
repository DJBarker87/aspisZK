# Own wrapper serialization; holds through admission, submission and recovery.
import fcntl
from pathlib import Path
_nbo_serial = (Path(__file__).resolve().parent / 'NBW_SERIAL.lock').open('a')
fcntl.flock(_nbo_serial, fcntl.LOCK_EX)
from NBW_host import *
import hashlib,tomllib,sys,os
attempt,harness=sys.argv[1:]
assert attempt.startswith('NBW_K') and int(attempt[5:])<=50
assert not (E/attempt/'receipt.json').exists()
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
env={'TMPDIR':B+'/NBW_tmp','PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_BUILD_JOBS':'1','CARGO_NET_OFFLINE':'true','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG':'0','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','RUSTFLAGS':'-C link-arg=-Wl,--threads=1'}
base=dict(source_revision=rev,source_tree_dirty=True,sources=['NBW_src/Cargo.lock','NBW_src/Cargo.toml','NBW_src/crates/aspis-r1-cost-probe/src/verifier.rs','NBW_src/crates/aspis-r1-cost-probe/src/candidate.rs','NBW_src/crates/aspis-r1-cost-probe/src/NBW_native.rs','NBW_src/crates/aspis-r1-cost-probe/src/KMX_stubs.rs','NBW_src/crates/aspis-r1-cost-probe/src/lib.rs'],env=env)
r=py(f'from pathlib import Path;Path({(B+"/NBW_tmp")!r}).mkdir(exist_ok=True)');assert r.returncode==0
before=ssh('sha256sum '+B+'/NBW_src/Cargo.lock');assert before.returncode==0
expected='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
assert before.stdout.split()[0]==expected
meta=attempt.replace('_K','_G')
r=launch(dict(base,attempt=meta,kind='metadata',command=['/home/dombarker/.cargo/bin/cargo','metadata','--manifest-path',B+'/NBW_src/Cargo.toml','--locked','--offline','--format-version','1'],timeout=120,expected_time='Frozen dependency graph validation before Kani, no proof'))
assert r['exit_status']==0
s=(E/meta/'stdout.log').read_text();pos=s.find('{');assert pos>=0
m=json.loads(s[pos:]);keys={p['id']:json.dumps([p['name'],p['version'],p.get('source')],separators=(',',':')) for p in m['packages']}
graph={'packages':sorted(keys.values()),'edges':sorted([keys[n['id']],sorted(keys[d] for d in n['dependencies'])] for n in m['resolve']['nodes'])}
assert graph==json.loads((E/'NBW_frozen_graph.json').read_text()),'STOP frozen graph changed'
check=dict(exact_frozen_resolved_graph_match=True,frozen_graph_sha256=hashlib.sha256((E/'NBW_frozen_graph.json').read_bytes()).hexdigest(),metadata_receipt=meta+'/receipt.json',lock_before_sha256=expected,lock_after_sha256=None)
(E/(attempt+'-graph-check.json')).write_text(json.dumps(check,indent=2)+'\n')
cmd=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NBW_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/NBW_target','--lib','-j','1','-Z','unstable-options','-Z','stubbing','--harness-timeout','90s','--exact','--harness',(harness if '::' in harness else 'verifier::candidate::NBW_native::'+harness),'--output-format',('regular' if os.getenv('NBW_DIAGNOSTIC') else 'terse')]
r=launch(dict(base,attempt=attempt,kind='kani',command=cmd,timeout=600,expected_time='Optimized compilation then '+harness+' native single-call gate',deps_fingerprint={'frozen_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','graph_check':attempt+'-graph-check.json'}))
after=ssh('sha256sum '+B+'/NBW_src/Cargo.lock');assert after.returncode==0
check['lock_after_sha256']=after.stdout.split()[0];check['lock_unchanged']=check['lock_after_sha256']==expected
(E/(attempt+'-graph-check.json')).write_text(json.dumps(check,indent=2)+'\n')
assert check['lock_unchanged'],'STOP Cargo.lock drift'
