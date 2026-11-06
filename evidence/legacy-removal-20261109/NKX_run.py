"""Own build/test driver, invoked inside one admitted capped scope."""
import pathlib,subprocess,json,hashlib,time,os,sys,re
B=pathlib.Path(__file__).resolve().parent; S=B/'src'; mode=sys.argv[1]; out=B/mode;out.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cg=pathlib.Path('/sys/fs/cgroup')/pathlib.Path('/proc/self/cgroup').read_text().split('0::')[1].strip().lstrip('/')
limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert list(limits.values())==['6442450944','8589934592','0','64']
assert __import__('shutil').disk_usage(B).free>=40_000_000_000
assert subprocess.check_output(['du','-sb',str(B)],text=True).split()[0].isdigit()
assert int(subprocess.check_output(['du','-sb',str(B)],text=True).split()[0])<20_000_000_000
lock=sha(S/'Cargo.lock')
env=os.environ.copy()
for k in list(env):
 if k.startswith(('CARGO_PROFILE_','ASPIS_')) or k in ['RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS']:env.pop(k)
env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_HOME='/home/dombarker/.cargo',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(B/'target'),CARGO_BUILD_JOBS='4')
features='r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit'
if mode.startswith(('baseline','tests')):
 cmd=['cargo','test','--manifest-path',str(S/'programs/aspis-pool/Cargo.toml'),'--release','--locked','--offline','-j','4']
 if mode!='tests-default':cmd+=['--features',features]
 if mode in ['tests-disabled','tests-all']:cmd[-1]+=',pair-afterstate-evidence,pair-forest-full-asf8-audit'
 if mode=='tests-all':cmd[-1]+=',pair-forest-history-page-invariant-audit,pair-forest-deposit-invariant-audit,pair-forest-direct-result-audit'
else:
 program='aspis-pool' if mode.startswith('pool') else 'r1-cost-probe'
 # build-sbf skips key generation when this output path exists. A directory
 # is an explicit non-key placeholder: never create/read/use a wallet key.
 artifact_dir=out/'artifacts';artifact_dir.mkdir()
 (artifact_dir/('aspis_pool-keypair.json' if program=='aspis-pool' else 'aspis_r1_cost_probe_program-keypair.json')).mkdir()
 pins={
 '/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf':'46e50d5d1bcc70abfd74f0b6281071ef91576031330d1d892622e1ea59445d6c',
 '/home/dombarker/.cache/solana/v1.52/platform-tools/rust/bin/rustc':'d95c95b68e321ad76634e1fd26b0a7c20ccdbae9ad9ca733f3ae2f2b4a0b6002',
 '/home/dombarker/project-offloads/codex-cx-lowering2-20261026/rustc-diagnostics.py':'fa74d69e097b6eab43809943614133081abb6beb19406018961402b86494ff84'}
 for p,h in pins.items():assert sha(pathlib.Path(p))==h,(p,'tool pin changed')
 cmd=['/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf','--manifest-path',str(S/'programs'/program/'Cargo.toml'),'--sbf-out-dir',str(out/'artifacts'),'--features',features if program=='aspis-pool' else 'pool-adapter,private-leaf-salts','--skip-tools-install','--offline','-j','4','--','--locked']
 env.update(CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4',RUSTC_WRAPPER='/home/dombarker/project-offloads/codex-cx-lowering2-20261026/rustc-diagnostics.py',S10_DIAGNOSTICS=str(out/'diagnostics'))
 if mode=='devnet':env.update(ASPIS_R1_POOL_PROGRAM_ID='BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs',ASPIS_R1_REGISTRY_PROGRAM_ID='9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q')
 if mode=='pool2':
  # Force fresh Pool codegen; retain unchanged dependencies for reproducibility.
  for p in (B/'target').glob('**/release/.fingerprint/aspis-pool-*'):
   __import__('shutil').rmtree(p)
  for p in (B/'target').glob('**/release/deps/*aspis_pool*'):
   if p.is_file():p.unlink()
rec=dict(attempt=mode,target=cmd,source_revision=(B/'NKX_revision.txt').read_text().strip(),source_tree_dirty=mode.startswith('tests'),driver_sha256=sha(pathlib.Path(__file__)),source_manifest={str(p.relative_to(S)):sha(p) for root in ['crates','programs'] for p in (S/root).rglob('*') if p.is_file()},limits=limits,cgroup=str(cg),disk_free_before_bytes=__import__('shutil').disk_usage(B).free,own_disk_before_bytes=int(subprocess.check_output(['du','-sb',str(B)],text=True).split()[0]),lock_before=lock,environment={k:v for k,v in env.items() if k.startswith(('CARGO_','RUST','S10_','ASPIS_'))},print_axioms='N/A: engineering build/test',expected_work='optimized compilation and native tests' if mode.startswith(('baseline','tests')) else 'optimized SBF compilation/linking')
meta=subprocess.run(['cargo','metadata','--manifest-path',str(S/'programs'/('aspis-pool' if mode.startswith(('baseline','tests','pool')) else 'r1-cost-probe')/'Cargo.toml'),'--features',cmd[cmd.index('--features')+1] if '--features' in cmd else '','--locked','--offline','--format-version','1'],cwd=S,env=env,capture_output=True,text=True)
assert meta.returncode==0,meta.stderr
metadata=json.loads(meta.stdout)
rec['resolved_packages']=[dict(id=n['id'],features=n['features']) for n in metadata['resolve']['nodes']]
assert sha(S/'Cargo.lock')==lock
rec['tool_pins']=pins if not mode.startswith(('baseline','tests')) else {}
rec['native_rustc_version']=subprocess.check_output(['rustc','--version'],cwd=S,env=env,text=True).strip()
(out/'command.json').write_text(json.dumps(rec,indent=1)+'\n')
t=time.monotonic()
with (out/'stdout.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v','-o',str(out/'time.log'),'timeout','600','taskset','--cpu-list','0-3',*cmd],cwd=S,env=env,stdout=f,stderr=subprocess.STDOUT)
rec.update(exit_status=r.returncode,wall_seconds=time.monotonic()-t,cgroup_memory_peak_bytes=(cg/'memory.peak').read_text().strip(),lock_after=sha(S/'Cargo.lock'))
s=(out/'time.log').read_text()
for key,label in [('peak_rss_kib','Maximum resident set size'),('swaps','Swaps')]:rec[key]=next((l.split(':',1)[1].strip() for l in s.splitlines() if label in l),None)
rec['artifacts']=[dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size) for p in (out/'artifacts').glob('*.so')]
rec['test_results']=re.findall(r'test result:.*', (out/'stdout.log').read_text())
(out/'receipt.json').write_text(json.dumps(rec,indent=1)+'\n')
print(json.dumps({k:rec[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','artifacts','test_results']}),flush=True)
assert rec['lock_before']==rec['lock_after'],'STOP: lock drift'
sys.exit(r.returncode)
