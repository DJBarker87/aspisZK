from pathlib import Path
from cooldown import check_ready,refuse
import subprocess,json,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-dlib-20261028';D='/home/dombarker/project-offloads/codex-pv-dlib-20261028';H='dombarker@100.108.41.90';G='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
check_ready();name=sys.argv[1];assert name.replace('-','').isalnum()
r=subprocess.run(['ssh',H,f'mkdir -p {D}/{name}; python3 {G}/reservation.py {D}/{name}/admission.json > {D}/{name}/reservation.log 2>&1'],capture_output=True,text=True)
a=subprocess.check_output(['ssh',H,f'cat {D}/{name}/admission.json'],text=True);(E/(name+'.json')).write_text(a)
if r.returncode!=0 or json.loads(a).get('allowed') is not True:
 refuse('staging '+name,{k:json.loads(a).get(k) for k in ['utc','allowed','error']});sys.exit(78)
for f in ['default-native-resume.rs','default-forward-helper.rs']:
 subprocess.run(['scp','-q',str(R/'tools/pv-dlib-20261028'/f),H+':'+D+'/wrapper-proof/'+f],check=True)
code='''from pathlib import Path
import hashlib,json
b=Path('/home/dombarker/project-offloads/codex-pv-dlib-20261028');p=b/'native/digest-0.10.7/src/core_api/wrapper.rs';s=p.read_text();assert 'pv_dl_owned_default' not in s
p.write_text(s+'\\n'+(b/'wrapper-proof/default-forward-helper.rs').read_text())
p=b/'wrapper-proof/Cargo.toml';s=p.read_text();assert 'default_native_resume' not in s
p.write_text(s+'\\n[[test]]\\nname="default_native_resume"\\npath="default-native-resume.rs"\\n')
print(json.dumps(dict(manifest_sha256=hashlib.sha256(p.read_bytes()).hexdigest())))
'''
r=subprocess.run(['ssh',H,'python3','-'],input=code,text=True,capture_output=True);(E/(name+'-source.json')).write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
