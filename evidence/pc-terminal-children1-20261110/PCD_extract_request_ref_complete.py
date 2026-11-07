from pathlib import Path
import subprocess,json,hashlib,os
B=Path(__file__).resolve().parent
C=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon')
A=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/aeneas-b59d5188-extended')
S=B/'PCD_request_ref'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
roots=['crate::request_ref']
namespace='PCD_FrozenRequest'
dest=B/'PCD_request_extracted'
cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or','--include','aspis_statement::pool_v1::pair_forest_accounts::PoolV1PairForestLaneStateV1','--include','aspis_statement::pool_v1::incremental_merkle::IncrementalMerkleTreeV1','--include','aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalResultV1','--include','aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1','--include','aspis_core::field::M31','--include','solana_program_error::ProgramError','--include','aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalRequestV1','--include','aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalPaymentV1','--include','aspis_statement::pool_v1::payment_relation::PoolV1PrivateTransferPublicV1','--include','aspis_statement::pool_v1::payment_relation::PoolV1WithdrawalPublicV1']
for root in roots:cmd+=['--start-from',root]
cmd+=['--dest-file',str(B/'PCD_request_ref.llbc'),'--','--manifest-path',str(S/'Cargo.toml'),'--offline','--locked','--release','--lib','--jobs','1']

env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'PCD_actual_extract_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
pins=dict(charon_sha256=sha(C),aeneas_sha256=sha(A),rust_reference_sha256=sha(S/'src/lib.rs'),charon_command=cmd,toolchain='nightly-2026-09-17',aeneas_origin='b59d5188 extended binary; imported read-only, no tool patches by NCO')
(B/'PCD_REF_CHARON_PINS.json').write_text(json.dumps(pins,indent=2))
print(json.dumps(pins),flush=True)
# Normalize only the standalone reference lock, then enforce a frozen-graph subset.
import tomllib
app=B/'PCD_src/Cargo.lock';frozen=tomllib.loads(app.read_text())
application_lock_before=sha(app)
m=subprocess.run(['/home/dombarker/.cargo/bin/cargo','metadata','--offline','--format-version','1','--manifest-path',str(S/'Cargo.toml')],cwd=S,env=env,capture_output=True,text=True)
(B/'PCD_REF_METADATA.stderr').write_text(m.stderr);assert m.returncode==0,m.stderr
metadata=json.loads(m.stdout);(B/'PCD_REF_METADATA.json').write_text(m.stdout)
ref=tomllib.loads((S/'Cargo.lock').read_text())
def key(p):return (p['name'],p['version'],p.get('source'))
frozen_by={key(p):p for p in frozen['package']}
def dependencies(p,packages):
 result=set()
 for d in p.get('dependencies',[]):
  words=d.split();name=words[0];version=words[1] if len(words)>1 and words[1][0].isdigit() else None
  selected=[key(q) for q in packages if q['name']==name and (version is None or q['version']==version)]
  assert len(selected)==1,(d,selected);result.add(selected[0])
 return result
for package in ref['package']:
 if package['name']=='pcd_request_ref':continue
 k=key(package);assert k in frozen_by,('STOP reference dependency drift',k)
 old=frozen_by[k];assert package.get('checksum')==old.get('checksum'),('checksum',k)
 assert dependencies(package,ref['package'])<=dependencies(old,frozen['package']),('STOP reference edge drift',k)
assert sha(app)==application_lock_before=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
(B/'PCD_REF_GRAPH_CHECK.json').write_text(json.dumps(dict(status='PASS',reference_lock_sha256=sha(S/'Cargo.lock'),application_lock_sha256=sha(app),new_package='pcd_request_ref 0.0.0 only',resolved_features_every_crate={node['id']:node['features'] for node in metadata['resolve']['nodes']},semantics='standalone extraction reference only; every non-root package identity/checksum and dependency edge is a frozen-lock subset'),indent=1)+'\n')

before=sha(S/'Cargo.lock')
application_lock_before=sha(B/'PCD_src/Cargo.lock')
r=subprocess.run(cmd,cwd=S,env=env)
assert sha(S/'Cargo.lock')==before,'STOP reference lock drift'
assert sha(B/'PCD_src/Cargo.lock')==application_lock_before=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef','STOP application lock drift'
if r.returncode:raise SystemExit(r.returncode)
pins.update(charon_exit=r.returncode,llbc_sha256=sha(B/'PCD_request_ref.llbc') if (B/'PCD_request_ref.llbc').exists() else None,phase='Charon ONLY after separately compiled dependency; no Aeneas in this scope')
(B/'PCD_REF_CHARON_PINS.json').write_text(json.dumps(pins,indent=2))
assert r.returncode==0

llbc=B/'PCD_request_ref.llbc'
assert sha(A)=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
aeneas=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','PCD_FrozenRequest','-dest',str(B/'PCD_ref_request_extracted'),'-subdir','PCD_FrozenRequest','-split-files',str(llbc)]
r=subprocess.run(aeneas,cwd=B)
(B/'PCD_REF_AENEAS_PINS.json').write_text(json.dumps(dict(aeneas_sha256=sha(A),llbc_sha256=sha(llbc),command=aeneas,exit=r.returncode,outputs={str(z.relative_to(B)):sha(z) for z in (B/'PCD_ref_request_extracted').rglob('*') if z.is_file()}),indent=1)+'\n')
raise SystemExit(r.returncode)
