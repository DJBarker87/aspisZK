import NCP_runner as m
from pathlib import Path
import sys,json,hashlib,subprocess
if (m.E/'NCP_PAUSE').exists():raise SystemExit('STOP own serial queue paused before launch')
if sys.argv[1]=='upload':
 m.admit('NCP_UPLOAD')
 text=(m.E/'NCP_controls.rs.txt').read_text()
 r=m.py(f"from pathlib import Path; Path({(m.B+'/NCP_src/crates/aspis-statement/src/NCP_controls.rs')!r}).write_text({text!r})");assert r.returncode==0,r.stderr
 sys.exit(0)
a,harness=sys.argv[1:]
assert len(list(m.E.glob('NCP_K*/receipt.json')))<70
sources=(['NCP_src/crates/aspis-statement/src/NCP_scalar.rs','NCP_src/crates/aspis-statement/src/pool_v1/pair_tree_profile.rs'] if harness.startswith('NCP_scalar::') else [])+(['NCP_src/crates/aspis-statement/src/pool_v1/pair_terminal.rs','NCP_src/crates/aspis-statement/src/pool_v1/pair_terminal/NCP_after.rs'] if 'NCP_after::' in harness else [])+(['NCP_src/crates/aspis-statement/src/NCP_loops.rs'] if (harness.startswith(('NCP_loops::','NCP_scalar::')) or 'NCP_after::NCP_after_' in harness or harness=='NCP_digest::NCP_encode_contract') else [])+(['NCP_src/crates/aspis-core/src/NCP_word.rs','NCP_src/crates/aspis-core/src/field.rs','NCP_src/crates/aspis-core/src/lib.rs'] if harness.startswith('NCP_word::') else [])+['NCP_src/crates/aspis-statement/src/atomic_statement.rs']+(['NCP_src/crates/aspis-core/src/lib.rs','NCP_src/crates/aspis-core/src/NCP_arbitrary.rs','NCP_src/crates/aspis-core/src/field.rs'] if harness.startswith('NCP_digest::') and (m.E/'NCP_arbitrary.rs.txt').exists() else [])+(['NCP_src/crates/aspis-statement/src/NCP_digest.rs'] if harness.startswith('NCP_digest::') else [])+['NCP_src/Cargo.lock','NCP_KMX_copy_stubs.patch','NCP_src/crates/aspis-statement/src/lib.rs','NCP_src/crates/aspis-statement/src/NCP_controls.rs','NCP_src/crates/aspis-statement/src/KMX_stubs.rs']
r=m.py(f"from pathlib import Path; import hashlib; b=Path({m.B!r}); p=b/'NCP_KMX_copy_stubs.patch'; assert hashlib.sha256(p.read_bytes()).hexdigest()=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'; assert (b/'NCP_src/KMX_stubs.rs').read_bytes()==(b/'NCP_src/crates/aspis-statement/src/KMX_stubs.rs').read_bytes()")
assert r.returncode==0,r.stderr
g=a.replace('_K','_G')
r=json.loads((m.E/g/'receipt.json').read_text()) if (m.E/g/'receipt.json').exists() else m.launch(g,'metadata',['/home/dombarker/.cargo/bin/cargo','metadata','--manifest-path',m.B+'/NCP_src/Cargo.toml','--locked','--offline','--format-version','1'],sources,120)
assert r['exit_status']==0
log=m.E/g/'stdout.log'; lines=log.read_text().splitlines();data=next(json.loads(s) for s in lines if s.startswith('{') and '"packages"' in s)
k={p['id']:json.dumps([p['name'],p['version'],p.get('source')],separators=(',',':')) for p in data['packages']}
graph={'packages':sorted(k.values()),'edges':sorted([k[n['id']],sorted(k[d] for d in n['dependencies'])] for n in data['resolve']['nodes'])}
expected=json.loads(subprocess.check_output(['git','show','HEAD:evidence/leaf-p6-11-20261027/LPm_frozen_graph.json'],text=True));assert graph==expected
frozen=hashlib.sha256(subprocess.check_output(['git','show',m.REV+':Cargo.lock'])).hexdigest()
before=m.ssh('sha256sum '+m.B+'/NCP_src/Cargo.lock').stdout.split()[0];assert before==frozen
check=dict(kmx_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',graph_matches_frozen=True,lock_before_sha256=before,frozen_lock_sha256=frozen,offline=True)
(m.E/(a+'-graph.json')).write_text(json.dumps(check,indent=2))
(m.E/g/'NCP_METADATA_PIN.json').write_text(json.dumps(dict(sha256=hashlib.sha256(log.read_bytes()).hexdigest(),bytes=log.stat().st_size,raw_retained_on_host=m.B+'/'+g+'/stdout.log')));log.unlink()
r=m.launch(a,'kani',['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',m.B+('/NCP_src/crates/aspis-core/Cargo.toml' if harness.startswith('NCP_word::') else '/NCP_src/crates/aspis-statement/Cargo.toml'),'--lib','-j','1','-Z','unstable-options','-Z','stubbing','-Z','function-contracts']+(['-Z','loop-contracts'] if (harness.startswith(('NCP_loops::','NCP_scalar::')) or 'NCP_after::NCP_after_' in harness or harness=='NCP_digest::NCP_encode_contract') else [])+['--harness-timeout','90s','--exact','--harness',harness,'--output-format','terse'],sources,600)
after=m.ssh('sha256sum '+m.B+'/NCP_src/Cargo.lock').stdout.split()[0];check.update(lock_after_sha256=after,lock_unchanged=after==before);(m.E/(a+'-graph.json')).write_text(json.dumps(check,indent=2));assert after==before
print((m.E/a/'stdout.log').read_text()[-6000:])
sys.exit(r['exit_status'])
