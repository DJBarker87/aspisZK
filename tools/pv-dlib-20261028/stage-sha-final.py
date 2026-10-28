"""Stage private native differential helpers, keeping shipped prefixes intact."""
from pathlib import Path
from cooldown import check_ready,refuse
import json,subprocess,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-dlib-20261028';D='/home/dombarker/project-offloads/codex-pv-dlib-20261028';H='dombarker@100.108.41.90';G='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
check_ready()
name=sys.argv[1];assert name.replace('-','').isalnum()
r=subprocess.run(['ssh',H,f'mkdir -p {D}/{name}; python3 {G}/reservation.py {D}/{name}/admission.json > {D}/{name}/reservation.log 2>&1'],capture_output=True,text=True)
a=subprocess.check_output(['ssh',H,f'cat {D}/{name}/admission.json'],text=True);(E/(name+'.json')).write_text(a)
if r.returncode!=0 or json.loads(a).get('allowed') is not True:
 refuse('staging '+name,{k:json.loads(a).get(k) for k in ['utc','allowed','error']});sys.exit(78)
for f in ['sha-final-helpers.rs','sha-final-native.rs']:
 subprocess.run(['scp','-q',str(R/'tools/pv-dlib-20261028'/f),H+':'+D+'/wrapper-proof/'+f],check=True)
code='''from pathlib import Path
import hashlib,json
b=Path(DIR);reg=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/sha2-0.10.9/src/core_api.rs')
p=b/'native/sha2-0.10.9/src/core_api.rs';s=p.read_text();source=reg.read_bytes();assert p.read_bytes().startswith(source)
helper=(b/'wrapper-proof/sha-final-helpers.rs').read_text();assert 'pv_dl_from_state' not in s
p.write_text(s+'\\n'+helper)
c=b/'wrapper-proof/Cargo.toml';s=c.read_text();assert 'sha_final_native' not in s
c.write_text(s+'\\n[[test]]\\nname="sha_final_native"\\npath="sha-final-native.rs"\\n')
print(json.dumps(dict(original_prefix_sha256=hashlib.sha256(source).hexdigest(),new_source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),helper_sha256=hashlib.sha256(helper.encode()).hexdigest(),original_prefix_intact=p.read_bytes().startswith(source))))
'''.replace('DIR',repr(D))
r=subprocess.run(['ssh',H,'python3','-'],input=code,text=True,capture_output=True);(E/(name+'-source.json')).write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
