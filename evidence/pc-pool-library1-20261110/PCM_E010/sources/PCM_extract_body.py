"""Fresh frozen-body route extraction only; no native proof or Kani."""
from pathlib import Path
import subprocess,json,hashlib,os,lzma,base64,sys
B=Path(__file__).resolve().parent;plan=json.loads((B/sys.argv[1]).read_text());a=plan['attempt'];S=B/'PCM_frozen_src'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files=json.loads(lzma.decompress((B/'PCM_EXTRACT_INPUTS.json.xz').read_bytes()))
for name,r in files.items():
 p=S/name;assert str(p.resolve()).startswith(str(S.resolve())+'/')
 data=base64.b64decode(r['base64']);assert hashlib.sha256(data).hexdigest()==r['sha256']
 p.parent.mkdir(parents=True,exist_ok=True)
 if p.exists():assert p.read_bytes()==data,str(p)
 else:p.write_bytes(data)
manifest={n:r['sha256'] for n,r in files.items() if n.startswith('programs/aspis-pool/')}
assert len(manifest)==20
for n,h in manifest.items():assert sha(S/n)==h,n
lock_before=sha(S/'Cargo.lock')
C=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon')
A=C.parent/'aeneas-b59d5188-extended'
tool=json.loads((B/'PCM_NCO_TOOL_PINS.json').read_text())
assert sha(C)==tool['charon_sha256'] and sha(A)==tool['aeneas_sha256']
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'PCM_extract_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
features='default,pair-forest-account-evidence,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit,pair-forest-verifier-lane-invariant-audit,r1-split-checkpoint'
pins=dict(attempt=a,phase=plan['phase'],roots=plan.get('roots',[]),toolchain=env['RUSTUP_TOOLCHAIN'],charon_sha256=sha(C),aeneas_sha256=sha(A),pool_files=manifest,lock_before=lock_before,expected_work='Compilation / fresh MIR and Lean emission only; no arithmetic gate, Kani, SHA unwind, native loop proof or whole-function native comparison',native_credit=False)
output=B/(a+'_pins.json')
if plan['phase'] in ['charon','both']:
 meta=['cargo','metadata','--manifest-path',str(S/'programs/aspis-pool/Cargo.toml'),'--format-version','1','--offline','--locked','--features',features]
 r=subprocess.run(meta,cwd=S,env=env,text=True,capture_output=True)
 (B/(a+'_metadata.stderr')).write_text(r.stderr)
 if r.returncode:
  pins.update(metadata_exit=r.returncode,metadata_error=r.stderr,lock_after=sha(S/'Cargo.lock'));output.write_text(json.dumps(pins,indent=1));sys.exit(r.returncode)
 m=json.loads(r.stdout);pkgs={x['id']:x for x in m['packages']}
 pins['resolved_packages']=[dict(id=x['id'],name=pkgs[x['id']]['name'],version=pkgs[x['id']]['version'],features=x['features']) for x in m['resolve']['nodes']]
 (B/(a+'_metadata.json')).write_text(r.stdout)
 cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default']
 for name in ['core::option::Option','core::result::Result','core::option::_::ok_or','aspis_statement::pool_v1::pair_forest_accounts::PoolV1PairForestLaneStateV1','aspis_statement::pool_v1::incremental_merkle::IncrementalMerkleTreeV1','aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalResultV1','aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1','aspis_core::field::M31','solana_program_error::ProgramError','aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalRequestV1','aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalPaymentV1','aspis_statement::pool_v1::payment_relation::PoolV1PrivateTransferPublicV1','aspis_statement::pool_v1::payment_relation::PoolV1WithdrawalPublicV1']:cmd+=['--include',name]
 for root in plan['roots']:cmd+=['--start-from',root]
 for root in plan.get('exclude',[]):cmd+=['--exclude',root]
 cmd+=['--dest-file',str(B/(a+'.llbc')),'--','--manifest-path',str(S/'programs/aspis-pool/Cargo.toml'),'--offline','--locked','--release','--lib','--jobs','1','--features',features]
else:
 llbc=B/plan['llbc'];assert sha(llbc)==plan['llbc_sha256']
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',plan['namespace'],'-dest',str(B/(a+'_emitted')),'-subdir',plan['namespace'],'-split-files',str(llbc)]
pins['command']=cmd;output.write_text(json.dumps(pins,indent=1));r=subprocess.run(cmd,cwd=S if plan['phase'] in ['charon','both'] else B,env=env)
if plan['phase']=='both':
 pins['charon_exit']=r.returncode
 if r.returncode==0:
  llbc=B/(a+'.llbc');pins['llbc_sha256']=sha(llbc)
  acmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',plan['namespace'],'-dest',str(B/(a+'_emitted')),'-subdir',plan['namespace'],'-split-files',str(llbc)]
  pins['aeneas_command']=acmd;output.write_text(json.dumps(pins,indent=1))
  r=subprocess.run(acmd,cwd=B,env=env)
pins.update(exit=r.returncode,lock_after=sha(S/'Cargo.lock'))
assert pins['lock_after']==lock_before,'STOP: frozen lock changed'
if (B/(a+'.llbc')).exists():pins['llbc_sha256']=sha(B/(a+'.llbc'))
pins['outputs']={str(p.relative_to(B)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in (B/(a+'_emitted')).rglob('*') if p.is_file()}
output.write_text(json.dumps(pins,indent=1)+'\n');sys.exit(r.returncode)
