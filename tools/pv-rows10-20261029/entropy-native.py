from pathlib import Path
import json,hashlib,subprocess,os
D=Path('/home/dombarker/project-offloads/codex-pv-rows10-20261029');O=D.parent/'codex-pv-ownd-20261029';P=O/'target/release/deps'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for p in json.loads((D/'dependency-source-pins.json').read_text()):assert sha(Path(p['path']))==p['sha256']
units=json.loads((O/'deployed-units.json').read_text())
u=next(u for u in units if u['package_id'].endswith('#getrandom@0.3.4') and u['target']['name']=='getrandom')
assert u['features']==['std'];assert not u['profile']['debug_assertions'] and not u['profile']['overflow_checks']
lib=P/'libgetrandom-fe336fb2b7d63711.rlib'
cmd=['rustc','+1.94.1','--edition=2021','-O','-C','debug-assertions=no','-C','overflow-checks=no','-C','panic=unwind','--cfg','feature="std"','--extern','getrandom='+str(lib),'--extern','libc='+str(next(P.glob('liblibc-*.rlib'))),'--extern','cfg_if='+str(next(P.glob('libcfg_if-*.rlib'))),'-L','dependency='+str(P),str(D/'entropy-native.rs'),'-o',str(D/'entropy-native')]
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'])
print('Expected time: small optimized harness compilation/link, then eight controlled-boundary tests and one live 64-byte fill',flush=True)
subprocess.run(cmd,env=env,check=True);q=subprocess.run([str(D/'entropy-native')],capture_output=True,text=True,check=True);print(q.stdout,flush=True)
r=dict(command=cmd,toolchain=subprocess.check_output(['rustc','+1.94.1','-Vv'],env=env,text=True),profile='release opt-level=3 debug-assertions=no overflow-checks=no panic=unwind',getrandom_unit=u,features_all_crates=units,binary_sha256=sha(D/'entropy-native'),binary_bytes=(D/'entropy-native').stat().st_size,inputs=[dict(path=str(p),sha256=sha(p)) for p in [lib,next(P.glob('liblibc-*.rlib')),next(P.glob('libcfg_if-*.rlib')),O/'deployed-units.json',O/'deployed-client-Cargo.lock',D/'entropy-native.rs',D/'entropy-native.py']],result=json.loads(q.stdout),compiler_boundary='V370 retained; source syscall boundary injected by closure; not shipped-binary execution',evidence_class='finite controlled-boundary validation of original dependency source')
(D/'native-result.json').write_text(json.dumps(r,indent=2)+'\n')
