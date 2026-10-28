"""Stage proof-only library copies with unchanged source prefixes and observers."""
from pathlib import Path
import subprocess,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-dlib-20261028';H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-pv-dlib-20261028'
g='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
r=subprocess.run(['ssh',H,f'mkdir -p {D}/stage-native; python3 {g}/reservation.py {D}/stage-native/admission.json > {D}/stage-native/reservation.log 2>&1'])
a=subprocess.check_output(['ssh',H,f'cat {D}/stage-native/admission.json'],text=True);(E/'stage-native-admission.json').write_text(a)
assert r.returncode==0 and json.loads(a).get('allowed') is True
code='''from pathlib import Path
import shutil,hashlib,json
b=Path(DIR);reg=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f');pins=[]
for name in ['sha2-0.10.9','digest-0.10.7','block-buffer-0.10.4']:
 src=reg/name;dst=b/'native'/name
 assert not dst.exists(),dst
 shutil.copytree(src,dst)
 for p in src.rglob('*'):
  if p.is_file():pins.append({'crate':name,'relative_path':str(p.relative_to(src)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
# Observers are appended under cfg(kani); every original source prefix remains intact.
p=b/'native/sha2-0.10.9/src/core_api.rs'
p.write_text(p.read_text()+"\\n#[cfg(kani)] impl Sha256VarCore { pub fn pv_dl_snapshot(&self)->([u32;8],u64) {(self.state,self.block_len)} }\\n")
p=b/'native/digest-0.10.7/src/core_api/ct_variable.rs'
p.write_text(p.read_text()+"\\n#[cfg(kani)] impl CtVariableCoreWrapper<sha2_placeholder, crypto_common::typenum::U32> {}\\n")
'''.replace('DIR',repr(D))
# The generic observer follows the existing impl bounds verbatim.
code=code[:code.index("p=b/'native/digest-0.10.7/src/core_api/ct_variable.rs'")]+'''
p=b/'native/digest-0.10.7/src/core_api/ct_variable.rs'
s=p.read_text();a=s.index('impl<T, OutSize, O> Default');c=s.index('{',a)
header=s[a:c].replace('Default for ','')
p.write_text(s+'\\n#[cfg(kani)] '+header+' { pub fn pv_dl_inner(&self)->&T { &self.inner } }\\n')
p=b/'native/block-buffer-0.10.4/src/lib.rs'
s=p.read_text();a=s.index('impl<BlockSize, Kind> Default');c=s.index('{',a)
header=s[a:c].replace('Default for ','')
p.write_text(s+'\\n#[cfg(kani)] '+header+' { pub fn pv_dl_bytes(&self)->&[u8] { &self.buffer } }\\n')
json.dump(pins,open(b/'native-prefix-pins.json','w'),indent=2)
print(json.dumps({'files':len(pins),'source_prefixes_preserved':True}))
'''
r=subprocess.run(['ssh',H,'python3','-'],input=code,text=True,capture_output=True);print(r.stdout,r.stderr);assert r.returncode==0
