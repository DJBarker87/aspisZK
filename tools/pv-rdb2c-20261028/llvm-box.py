from pathlib import Path
import subprocess,os,json,re,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2c-20261028');P=D/'weights-fixture'
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1',CARGO_TARGET_DIR=str(D/'target-weights'),CARGO_BUILD_JOBS='4',RUSTC_BOOTSTRAP='1',RUSTFLAGS='-Zdump-mir=box_from_parts -Zdump-mir-dir='+str(D/'box-mir'))
env['RUSTFLAGS']+=' --emit=llvm-ir,link'
cmd=['cargo','build','--manifest-path',str(P/'Cargo.toml'),'--release','--locked','--bin','fixture','-j','4','-v']
print('expected phase: optimized compilation to obtain missing intrinsic-lowering LLVM artifact; no native test rerun',flush=True)
j=json.loads((D/'weights-inputs.json').read_text());j.update(command=cmd,reason='runtime MIR still calls Box::new; LLVM is needed to audit the actual box_new allocation/write lowering',expected_phase='optimized compiler diagnostic emission, not proof generation or elimination')
(D/'box-llvm-inputs.json').write_text(json.dumps(j,indent=2))
r=subprocess.run(cmd,env=env);assert r.returncode==0
records=[];bodies=[]
for p in (D/'target-weights/release/deps').glob('aspis_r1_cost_probe-*.ll'):
 raw=p.read_bytes();records.append(dict(path=str(p),sha256=hashlib.sha256(raw).hexdigest(),size=len(raw)))
 for match in re.finditer(r'^define [^\n]*box_from_parts[^\n]*\{.*?^}',raw.decode(),re.M|re.S):bodies.append(match[0])
assert len(bodies)==1,len(bodies)
(D/'box-lowering.ll.txt').write_text(bodies[0]+'\n')
(D/'box-llvm-manifest.json').write_text(json.dumps(records,indent=2));print(bodies[0]);print('LLVM artifact records',json.dumps(records))
