from pathlib import Path
import hashlib,json,subprocess,sys,re,shlex
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/s2f-20261023';T=Path(__file__).parent
HOST='dombarker@100.108.41.90';H='/home/dombarker/project-offloads/codex-cx-s2f-20261023'
kind,num,target=sys.argv[1:4];attempt=f'{kind}-{int(num):03d}'
assert kind in ['lean','kani'];assert int(num)<=(100 if kind=='lean' else 60)
assert not (E/attempt).exists()
subprocess.run(['ssh',HOST,'mkdir','-p',H],check=True)
for name in ['S2F_run_host.py','S2F_reservation.py','S2F_cc']:
 subprocess.run(['scp',str(T/name),HOST+':'+H+'/'+name],check=True,stdout=subprocess.DEVNULL)
env={'PATH':'/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','CARGO_BUILD_JOBS':'4','CARGO_NET_OFFLINE':'true','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG':'0','RUSTFLAGS':'-C link-arg=-Wl,--threads=1'}
if kind=='kani':
 env['CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_LINKER']=H+'/S2F_cc'
 subprocess.run(['rsync','-az',str(E/'S2F-steps')+'/',HOST+':'+H+'/S2F-steps/'],check=True)
 source=['S2F-steps/Cargo.toml','S2F-steps/src/S2F_Trusted.rs','S2F-steps/src/lib.rs','S2F-steps/src/S2F_NativeCuts.rs','S2F-steps/src/S2F_CopyStub.rs']
 command=['cargo-kani','kani','--manifest-path','S2F-steps/Cargo.toml','--target-dir','kani-target','-j','4','-Z','stubbing','-Z','function-contracts','-Z','unstable-options','--harness-timeout','120s','--exact','--harness',target,'--output-format','terse']
 deps={'trusted_spec_sha256':hashlib.sha256((E/'S2F-steps/src/S2F_Trusted.rs').read_bytes()).hexdigest(),'reused_contract':'s2a-20261023/kani-003 (three cells, three tokens, two payload coordinates)','copy_contract_reuse':json.loads((E/'S2F-copy-reuse.json').read_text()),'reference_source':json.loads((E/'S2F-stage0.json').read_text())['sources'],'qualification':'Source cut projections only; no typed native Library or SBF admission instance.'}
else:
 source=[p.name for p in sorted((D/'lean').glob('S2F_*.lean'))]
 for name in source: subprocess.run(['scp',str(D/'lean'/name),HOST+':'+H+'/'+name],check=True,stdout=subprocess.DEVNULL)
 prior=json.loads((D/'evidence/s2e-20261023/lean-023.json').read_text())
 env={'LEAN_PATH':'.:/home/dombarker/project-offloads/codex-cx-s2e-20261023:'+prior['env']['LEAN_PATH']}
 deps=prior['deps_fingerprint']
 needed=set()
 def visit(name):
  for child in re.findall(r'^import (S2F_\w+)',(D/'lean'/(name+'.lean')).read_text(),re.M):
   if child not in needed:
    needed.add(child);visit(child)
 visit(target)
 records={}
 for name in sorted(needed):
  receipts=[json.loads(p.read_text()) for p in sorted(E.glob('lean-*/receipt.json'))]
  accepted=[r for r in receipts if r['exit_status']==0 and r['command'][-1]==name+'.lean']
  assert accepted, 'No successful predecessor: '+name
  previous=accepted[-1]
  current_sha=hashlib.sha256((D/'lean'/(name+'.lean')).read_bytes()).hexdigest()
  assert previous['source_hashes'][name+'.lean']==current_sha, 'Changed predecessor not compiled: '+name
  records[name]={'path':H+'/'+name+'.olean','source_sha256':current_sha,'accepted_attempt':previous['attempt']}
 remote="from pathlib import Path; import json,hashlib; r="+repr(records)+"; "+"\nfor v in r.values():\n p=Path(v['path']); v.update(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)\nprint(json.dumps(r))"
 if records:
  selected=json.loads(subprocess.check_output(['ssh',HOST,'python3 -c '+shlex.quote(remote)],text=True))
  deps['selected_objects'].update(selected)
 command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M4400','-DElab.async=false','-o',target+'.olean',target+'.lean']
 subprocess.run(['ssh',HOST,f"cd {H} && printf 'name = \"s2f\"\nversion = \"0.1.0\"\n' > lakefile.toml && printf 'leanprover/lean4:v4.32.0\n' > lean-toolchain"],check=True)
cfg=dict(attempt=attempt,kind=kind,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),command=command,sources=source,timeout=180,deps_fingerprint=deps,env=env,expected_time='cached optimized compilation then one named source-cut verification; no cryptographic arithmetic' if kind=='kani' else 'one focused Lean module against pinned cached objects')
(E/(attempt+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
subprocess.run(['scp',str(E/(attempt+'.json')),HOST+':'+H+'/'+attempt+'.json'],check=True,stdout=subprocess.DEVNULL)
r=subprocess.run(['ssh',HOST,f'cd {H} && python3 S2F_reservation.py {attempt}-reservation.json && systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2F_run_host.py {attempt}.json'])
subprocess.run(['scp','-r',HOST+':'+H+'/'+attempt,str(E/attempt)],check=True,stdout=subprocess.DEVNULL)
subprocess.run(['scp',HOST+':'+H+'/'+attempt+'-reservation.json',str(E)],check=True,stdout=subprocess.DEVNULL)
sys.exit(r.returncode)
