"""Check the entire shipped Ct method and the identical-body owned helper."""
from pathlib import Path
import subprocess,json,hashlib,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-dlib-20261028'
def clean(s):return re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S)
def tokens(s):return re.findall(r'::|=>|[A-Za-z_]\w*|\d+|[^\s]',clean(s))
def body(s,needle):
 s=clean(s);a=s.index('{',s.index(needle));d=0
 for i in range(a,len(s)):
  if s[i]=='{':d+=1
  elif s[i]=='}':
   d-=1
   if not d:return s[a:i+1]
 raise ValueError(needle)
code='''from pathlib import Path
import json,hashlib
r=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/digest-0.10.7/src/core_api/ct_variable.rs');b=Path('/home/dombarker/project-offloads/codex-pv-dlib-20261028')
s=r.read_bytes();p=b/'native/digest-0.10.7/src/core_api/ct_variable.rs';assert p.read_bytes().startswith(s)
print(json.dumps(dict(path=str(r),sha256=hashlib.sha256(s).hexdigest(),source=r.read_text(),helper=(b/'wrapper-proof/ct-owned-helper.rs').read_text())))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
j=json.loads(r.stdout);src=j.pop('source');helper=j.pop('helper');native=body(src,'fn finalize_fixed_core(');owned=body(helper,'pub fn pv_dl_owned_finalize_fixed_core(')
assert tokens(native)==tokens(owned)
expected='''{let mut full_res=Default::default();self.inner.finalize_variable_core(buffer,&mut full_res);
 let n=out.len();let m=full_res.len()-n;match T::TRUNC_SIDE {
 TruncSide::Left=>out.copy_from_slice(&full_res[..n]),TruncSide::Right=>out.copy_from_slice(&full_res[m..]),}}'''
assert tokens(native)==tokens(expected)
assert 'OutSize: ArrayLength<u8> + IsLessOrEqual<T::OutputSize>' in src
assert 'LeEq<OutSize, T::OutputSize>: NonZero' in src
out=dict(row='V238',evidence_class='structural (K-1 substitute)',rulings=['r',"k'"],source=j,native_body=native,owned_body=owned,whole_body_token_equal=True,owned_helper_sha256=hashlib.sha256(helper.encode()).hexdigest(),differences=[dict(native='trait implementation method',reference='public inherent helper with renamed method and explicitly qualified OutputSize type; identical body',proof='CtCarrier.complete, CtFinal.complete; original variable finalizer and truncation-side Result are parameters'),dict(native='GenericArray output storage and copy_from_slice',reference='binary even/odd carrier flattened to byte list, prefix or suffix followed by rebuilding same native carrier',proof='ArrayShape.flatten_build/reconstruct/length, CtCarrier.decoded, Truncation.length/full; native compile-time size guard unchanged')],complete_result='PV_DL_CtCarrier.complete',scope='Original SHA-cohort full32 bytes; output native even/odd shape size <=32, both sides; original64-byte Eager buffer. Original finalizer failures/divergence preserved; all returned inner state and buffer retained. No compression semantics.',finite_validation='../wrappers-native-combined-resume4/receipt.json',finite_scope='1024 paired same-input native/identical-body Ct fixtures, left/right28/32, changed core/all64buffer bytes; finite validation only',v232_untouched=True,kani=False)
(E/'V238/structural-binding.json').write_text(json.dumps(out,indent=2)+'\n');print('Ct whole body and helper tokens equal; original size constraints present')
