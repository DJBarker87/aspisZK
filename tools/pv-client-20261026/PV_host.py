#!/usr/bin/env python3
"""Use unchanged reviewed admission/receipt runners in this job's private host dir."""
import hashlib,json,pathlib,shlex,subprocess,sys
ROOT=pathlib.Path(__file__).resolve().parents[2]
REMOTE='/home/dombarker/project-offloads/codex-pv-client-20261026'
HOST='dombarker@100.108.41.90'
label=sys.argv[1]
e=ROOT/'evidence/pv-client-20261026'; t=ROOT/'tools/pv-client-20261026'
roots=['Cargo.toml','Cargo.lock','.cargo','crates','programs','tools/r1-cost-probe','xtask','audit/poseidon-pair-probe','docs/research/v8-r0-zk-20261009/z4','docs/research/v8-r0-zk-20261009/c3','docs/research/v8-r0-zk-20261009/refine']
files=[p for p in subprocess.check_output(['git','ls-files',*roots],cwd=ROOT,text=True).splitlines() if (ROOT/p).is_file()]
hashes={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in files}
manifest=e/(label+'-inputs.json');manifest.write_text(json.dumps(hashes,indent=2,sort_keys=True)+'\n')
cfg=dict(attempt=label,kind='optimized Rust client gate',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,expected_time='Optimized incremental compilation/link and tiny account-policy tests' if label.startswith('unit-') else 'Optimized incremental compilation, actual planner proof generation, then named pinned-ELF stage1/stage2/Pool execution',command=sys.argv[2:],timeout=1800,sources=['src/'+p for p in ['tools/r1-cost-probe/src/bin/devnet_spend.rs','tools/r1-cost-probe/src/bin/devnet_spend/plan.rs','tools/r1-cost-probe/src/bin/devnet_spend/Client64_accounts.rs']],env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=REMOTE+'/native-target',RUSTFLAGS='-C link-arg=-Wl,--threads=4',CARGO_BUILD_JOBS='4'),deps_fingerprint={'manifest_sha256':hashlib.sha256(manifest.read_bytes()).hexdigest(),'manifest':manifest.name})
config=e/(label+'-config.json');config.write_text(json.dumps(cfg,indent=2)+'\n')
subprocess.run(['scp','-q',str(config),str(manifest),HOST+':'+REMOTE+'/'],check=True)
verify="import hashlib,json,pathlib; h=json.load(open('"+manifest.name+"')); assert all(hashlib.sha256((pathlib.Path('src')/p).read_bytes()).hexdigest()==v for p,v in h.items())"
launch=f'python3 Port13GATE_admission.py > {label}-reservation.json && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 Port13GATE_run_host.py {config.name}'
command=f'cd {REMOTE} && python3 -c {shlex.quote(verify)} && flock /tmp/aspis-r0-lean.lock sh -c {shlex.quote(launch)}'
result=subprocess.run(['ssh',HOST,command],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
(e/(label+'-launcher.log')).write_text(result.stdout)
print(result.stdout)
subprocess.run(['scp','-q',HOST+':'+REMOTE+'/'+label+'-reservation.json',str(e)],check=True)
reservation=json.loads((e/(label+'-reservation.json')).read_text())
if reservation.get('admitted'):
 subprocess.run(['scp','-qr',HOST+':'+REMOTE+'/'+label,str(e)],check=True)
else:
 print('Admission refused; no scope ran. Retain the reservation and apply the common-rule retry cadence.')
sys.exit(result.returncode)
