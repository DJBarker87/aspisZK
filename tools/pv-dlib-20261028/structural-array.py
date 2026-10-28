"""Read-only structural K-1 substitute gate for the shipped generic Vec move."""
from pathlib import Path
import subprocess,json,hashlib,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-dlib-20261028'
expected='''{
 if vec.len()!=N {return Err(vec);}
 unsafe {vec.set_len(0)};
 let array=unsafe {ptr::read(vec.as_ptr() as *const [T;N])};
 Ok(array)
}'''
owned_expected='''{
 if v.len()!=N {return Err(v);}
 let mut iter=v.into_iter();
 Ok(core::array::from_fn(|_|iter.next().expect("length checked")))
}'''
def tokens(s):
 s=re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S)
 return re.findall(r'::|=>|[A-Za-z_]\w*|\d+|[^\s]',s)
def body(s,needle):
 a=s.index('{',s.index(needle));d=0
 for i in range(a,len(s)):
  if s[i]=='{':d+=1
  elif s[i]=='}':
   d-=1
   if not d:return s[a:i+1]
 raise ValueError(needle)
code='''from pathlib import Path
import json,hashlib
r=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
files={}
for n in ['alloc/src/vec/mod.rs','alloc/src/vec/into_iter.rs','core/src/array/mod.rs']:
 p=r/n;files[n]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),source=p.read_text())
print(json.dumps(files))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
files=json.loads(r.stdout);native=body(files['alloc/src/vec/mod.rs']['source'],'fn try_from(mut vec: Vec<T, A>)')
assert tokens(native)==tokens(expected),'shipped generic conversion body changed'
p=R/'tools/pv-dlib-20261028/array-owned-reference.rs';owned=body(p.read_text(),'pub fn array_owned')
assert tokens(owned)==tokens(owned_expected),'owned reference changed'
helpers=[]
for path,needle in [('alloc/src/vec/into_iter.rs','fn next(&mut self) -> Option<T>'),('core/src/array/mod.rs','const fn try_from_fn_erased')]:
 s=files[path]['source'];helpers.append(dict(path=files[path]['path'],body=body(s,needle),source_sha256=files[path]['sha256']))
# Both implementations are generic over unconstrained T, including ZST/Drop.
j=dict(evidence_class='structural (K-1 substitute)',rulings=['r','k\''],
 native=dict(path=files['alloc/src/vec/mod.rs']['path'],source_sha256=files['alloc/src/vec/mod.rs']['sha256'],complete_body=native,tokens_match=True),
 owned=dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),complete_body=owned,tokens_match=True),
 helper_bodies=helpers,
 differences=[dict(native='set_len(0), bulk ptr::read of [T;N]',owned='N forward IntoIter::next reads into from_fn',proofs=['PV_DL_ArrayTransfer.exact_transfer','PV_DL_ArrayTransfer.complete'],meaning='all N source elements transfer in original order; no unwrap failure and empty residual live region'),
 dict(native='Vec drop has len0',owned='IntoIter drop has no remaining elements',proofs=['PV_DL_ArrayTransfer.zero_live_drops'],meaning='neither destructor visits any T; no Copy/Clone restriction'),
 dict(native='length mismatch returns original Vec',owned='same branch before creating iterator',proofs=['PV_DL_ArrayOwnership.rejection'],meaning='allocation, capacity and live elements retained without reads'),
 dict(native='ZST: bulk read has zero byte extent',owned='ZST iterator decrements end byte count',proofs=['PV_DL_ArrayTransfer.exact_transfer'],meaning='logical element count/order and later destructor ownership do not depend on sizeof(T)')],
 complete_result_laws=['R1Z.PV_DL_ArrayOwnership.complete','R1Z.PV_DL_ArrayTransfer.complete'],
 extraction='Exact shipped generic entry Charon accepted; pinned Aeneas rejected structured Drop; unchanged refusal reused.',
 scope='selected op36 value/ownership callback law; no whole-prover timing or allocator failure law claimed',kani=False)
(E/'V187/structural-binding.json').write_text(json.dumps(j,indent=2)+'\n');print('generic native/owned complete bodies pinned; explicit ownership differences recorded')
