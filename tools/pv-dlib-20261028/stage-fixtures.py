from pathlib import Path
import json,subprocess,sys,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-dlib-20261028';D='/home/dombarker/project-offloads/codex-pv-dlib-20261028';H='dombarker@100.108.41.90';G='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
name=sys.argv[1];assert name in ['wrapper','array']
r=subprocess.run(['ssh',H,f'mkdir -p {D}/stage-{name}; python3 {G}/reservation.py {D}/stage-{name}/admission.json > {D}/stage-{name}/reservation.log 2>&1'])
a=subprocess.check_output(['ssh',H,f'cat {D}/stage-{name}/admission.json'],text=True);(E/f'stage-{name}-admission.json').write_text(a)
if r.returncode!=0 or json.loads(a).get('allowed') is not True:sys.exit(78)
subprocess.run(['ssh',H,f'mkdir -p {D}/{name}-proof'],check=True)
fs={'wrapper':['wrapper-native.rs','wrapper-native-entry.rs','padding-retained-reference.rs'],'array':['array-native.rs']}[name]
for f in fs:subprocess.run(['scp',str(R/'tools/pv-dlib-20261028'/f),H+':'+D+f'/{name}-proof/'+f],check=True)
manifest={'wrapper':'WrapperCargo.toml.txt','array':'ArrayCargo.toml.txt'}[name]
subprocess.run(['scp',str(R/'tools/pv-dlib-20261028'/manifest),H+':'+D+f'/{name}-proof/Cargo.toml'],check=True)
(E/f'{name}-fixture-source-pins.json').write_text(json.dumps({f:hashlib.sha256((R/'tools/pv-dlib-20261028'/f).read_bytes()).hexdigest() for f in fs+[manifest]},indent=2)+'\n')
