"""Check the exact one-iteration source fission; no native verdict is inferred."""
from pathlib import Path
import subprocess,re,hashlib,json
E=Path(__file__).resolve().parent;R=E.parent.parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def tok(s):return re.findall(r"[A-Za-z_][A-Za-z_0-9]*|[0-9]+|::|->|==|!=|<=|>=|\+=|[^\s]",s)
def check(native=None,frozen=None):
 if native is None:native=(E/'NET_prefix.rs.txt').read_text()
 path='crates/aspis-r1-cost-probe/src/verifier.rs'
 if frozen is None:frozen=subprocess.check_output(['git','show',REV+':'+path],cwd=R,text=True)
 start=frozen.index('fn batch_prefix_products(');end=frozen.index('\nimpl QueryGeometry',start)
 body=frozen[start:end];step=body[body.index('let value=flat[index];'):body.index('\n    }')]
 helper=native[native.index(' let value=flat[index];'):native.index('\n (product,index)')]
 erased=helper.replace('let product=NET_product(product,value,reply,log);','product=product.mul(value);').replace('let index=index+1;','index+=1;')
 assert tok(erased)==tok(step),'changed frozen iteration/order/operands'
 assert 'flat:&[M31]' in body and 'let mut product=M31::ONE;' in body
 assert 'Vec::with_capacity(flat.len())' in body and 'while index<flat.len()' in body
 assert 'NET_ProductLog{a:a.0,b:b.0,reply:reply.0};reply' in native
 assert not any(x in native for x in ['static mut','UnsafeCell','RefCell','Atomic','Option<fn','proof_for_contract','stub_verified'])
 assert 'kani::assume(i<M)' in native and 'while initialized<i' in native
 assert 'MaybeUninit::<M31>::uninit()' in native and 'Vec::from_raw_parts(p,i,M)' in native
 assert all(f'prefix!(NET_prefix_{n:02},{n*5});' in native for n in range(1,23))
 return dict(frozen_revision=REV,source_file=path,body_sha256=hashlib.sha256(body.encode()).hexdigest(),helper_sha256=hashlib.sha256(helper.encode()).hexdigest(),erasure='One active frozen iteration, local product log; no native multiplication',capacity_classes=list(range(5,111,5)),rule16='local record only',initialization='only logical length initialized; spare capacity uninitialized',status='SOURCE_ONLY; native and Lean certificates required')
if __name__=='__main__':print(json.dumps(check(),indent=1))
