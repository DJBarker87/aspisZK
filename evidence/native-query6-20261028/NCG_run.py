# Own wrapper serialization; holds through admission, submission and recovery.
import fcntl
from pathlib import Path
_nbo_serial = (Path(__file__).resolve().parent / 'NCG_SERIAL.lock').open('a')
fcntl.flock(_nbo_serial, fcntl.LOCK_EX)
from NCG_host import *
import hashlib,tomllib,sys,os
attempt,harness=sys.argv[1:]
if (E/'NCG_REDIRECT_REQUEST').exists():
 (E/'NCG_REDIRECT_ACK.json').write_text(json.dumps(dict(not_submitted=attempt,reason='independent coefficient-read gate next'))+'\n')
 raise SystemExit('Own queue redirected before metadata or submission')
assert attempt.startswith('NCG_K')
assert len(list(E.glob('NCG_K[0-9][0-9][0-9].json')))<80, 'Kani budget exhausted'
assert not (E/(attempt+'.json')).exists(), 'submitted attempt must only be recovered, never resubmitted'
assert not (E/attempt/'receipt.json').exists()
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
env={'TMPDIR':B+'/NCG_tmp','PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_BUILD_JOBS':'1','CARGO_NET_OFFLINE':'true','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG':'0','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','RUSTFLAGS':'-C link-arg=-Wl,--threads=1'}
base=dict(source_revision=rev,source_tree_dirty=True,sources=['NCG_src/Cargo.lock','NCG_src/Cargo.toml','NCG_src/crates/aspis-r1-cost-probe/src/verifier.rs','NCG_src/crates/aspis-r1-cost-probe/src/candidate.rs','NCG_src/crates/aspis-r1-cost-probe/src/NCG_native.rs','NCG_src/crates/aspis-r1-cost-probe/src/KMX_stubs.rs','NCG_src/crates/aspis-r1-cost-probe/src/lib.rs'],env=env)
base['sources'] += json.loads(os.getenv('NCG_EXTRA_SOURCES','[]'))
r=py(f'from pathlib import Path;Path({(B+"/NCG_tmp")!r}).mkdir(exist_ok=True)');assert r.returncode==0
before=ssh('sha256sum '+B+'/NCG_src/Cargo.lock');assert before.returncode==0
expected='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
assert before.stdout.split()[0]==expected
meta=attempt.replace('_K','_G')
r=launch(dict(base,attempt=meta,kind='metadata',command=['/home/dombarker/.cargo/bin/cargo','metadata','--manifest-path',B+'/NCG_src/Cargo.toml','--locked','--offline','--format-version','1'],timeout=120,expected_time='Frozen dependency graph validation before Kani, no proof'))
assert r['exit_status']==0
s=(E/meta/'stdout.log').read_text();pos=s.find('{');assert pos>=0
m=json.loads(s[pos:]);keys={p['id']:json.dumps([p['name'],p['version'],p.get('source')],separators=(',',':')) for p in m['packages']}
graph={'packages':sorted(keys.values()),'edges':sorted([keys[n['id']],sorted(keys[d] for d in n['dependencies'])] for n in m['resolve']['nodes'])}
assert graph==json.loads((E/'NCG_frozen_graph.json').read_text()),'STOP frozen graph changed'
check=dict(exact_frozen_resolved_graph_match=True,frozen_graph_sha256=hashlib.sha256((E/'NCG_frozen_graph.json').read_bytes()).hexdigest(),metadata_receipt=meta+'/receipt.json',lock_before_sha256=expected,lock_after_sha256=None)
(E/(attempt+'-graph-check.json')).write_text(json.dumps(check,indent=2)+'\n')
cmd=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NCG_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/NCG_target','--lib','-j','1','-Z','unstable-options','-Z','stubbing','-Z','function-contracts','--harness-timeout','90s','--exact','--harness',(harness if '::' in harness else 'verifier::candidate::NCG_native::'+harness),'--output-format',('regular' if os.getenv('NCG_DIAGNOSTIC') else 'terse')]
r=launch(dict(base,attempt=attempt,kind='kani',command=cmd,timeout=600,expected_time='Optimized compilation then '+harness+' native single-call gate',deps_fingerprint={'frozen_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','graph_check':attempt+'-graph-check.json'}))
after=ssh('sha256sum '+B+'/NCG_src/Cargo.lock');assert after.returncode==0
check['lock_after_sha256']=after.stdout.split()[0];check['lock_unchanged']=check['lock_after_sha256']==expected
(E/(attempt+'-graph-check.json')).write_text(json.dumps(check,indent=2)+'\n')
assert check['lock_unchanged'],'STOP Cargo.lock drift'
if r['exit_status']!=0:
 cleanup=py(f'''from pathlib import Path
import json,hashlib
root=Path({(B+'/NCG_tmp')!r});removed=[]
for p in root.rglob('*'):
 if p.is_file() and ((p.name.startswith('external-sat') and p.suffix=='.cnf') or p.name.startswith('smt2_dec_problem')):
  removed.append(dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()));p.unlink()
print(json.dumps(dict(attempt={attempt!r},removed=removed)))
''')
 assert cleanup.returncode==0,cleanup.stderr
 (E/(attempt+'-solver-cleanup.json')).write_text(cleanup.stdout)
