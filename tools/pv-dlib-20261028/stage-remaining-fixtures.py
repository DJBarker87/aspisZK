"""Stage remaining focused native fixtures together; original prefixes preserved."""
from pathlib import Path
from cooldown import check_ready,refuse
import subprocess,json,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-dlib-20261028';D='/home/dombarker/project-offloads/codex-pv-dlib-20261028';H='dombarker@100.108.41.90';G='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
check_ready();name=sys.argv[1];assert name.replace('-','').isalnum()
r=subprocess.run(['ssh',H,f'mkdir -p {D}/{name}; python3 {G}/reservation.py {D}/{name}/admission.json > {D}/{name}/reservation.log 2>&1'],capture_output=True,text=True)
a=subprocess.check_output(['ssh',H,f'cat {D}/{name}/admission.json'],text=True);(E/(name+'.json')).write_text(a)
if r.returncode!=0 or json.loads(a).get('allowed') is not True:
 refuse('staging '+name,{k:json.loads(a).get(k) for k in ['utc','allowed','error']});sys.exit(78)
for f in ['default-native-resume.rs','default-forward-helper.rs','ct-final-native.rs','update-native-resume.rs','default-reference.rs']:
 subprocess.run(['scp','-q',str(R/'tools/pv-dlib-20261028'/f),H+':'+D+'/wrapper-proof/'+f],check=True)
code='''from pathlib import Path
import hashlib,json
b=Path('/home/dombarker/project-offloads/codex-pv-dlib-20261028');reg=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/digest-0.10.7/src/core_api');records={}
p=b/'native/digest-0.10.7/src/core_api/wrapper.rs';s=p.read_text();assert p.read_bytes().startswith((reg/'wrapper.rs').read_bytes());assert 'pv_dl_owned_default' not in s
p.write_text(s+'\\n'+(b/'wrapper-proof/default-forward-helper.rs').read_text());records['wrapper_sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
p=b/'native/digest-0.10.7/src/core_api/ct_variable.rs';s=p.read_text();assert p.read_bytes().startswith((reg/'ct_variable.rs').read_bytes());assert 'pv_dl_owned_finalize_fixed_core' not in s
begin=s.index('impl<T, OutSize, O> FixedOutputCore for CtVariableCoreWrapper<T, OutSize, O>');a=s.index('{',begin);depth=0;end=None
for i in range(a,len(s)):
 if s[i]=='{':depth+=1
 elif s[i]=='}':
  depth-=1
  if depth==0:end=i+1;break
assert end
copy=s[begin:end].replace('FixedOutputCore for ','',1).replace('fn finalize_fixed_core(','pub fn pv_dl_owned_finalize_fixed_core(',1).replace('GenericArray<u8, Self::OutputSize>','GenericArray<u8, <Self as OutputSizeUser>::OutputSize>')
p.write_text(s+'\\n'+copy+'\\n');(b/'wrapper-proof/ct-owned-helper.rs').write_text(copy+'\\n');records['ct_helper']=copy;records['ct_sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
p=b/'wrapper-proof/Cargo.toml';s=p.read_text()
for name,file in [('default_native_resume','default-native-resume.rs'),('ct_final_native','ct-final-native.rs'),('update_native_resume','update-native-resume.rs')]:
 assert name not in s
 s+='\\n[[test]]\\nname="'+name+'"\\npath="'+file+'"\\n'
p.write_text(s);records['manifest_sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
print(json.dumps(records))
'''
r=subprocess.run(['ssh',H,'python3','-'],input=code,text=True,capture_output=True);(E/(name+'-source.json')).write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
