"""Strict source checks on the changed reserve proof shape, no root promotion."""
from pathlib import Path
import sys,json,hashlib
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent
sys.path.insert(0,str(E.parent/'slice-q-compose3-20261102'))
import NET_geometry_source as inherited
from NET_inverse_checks import functions,tok

def check(source=None):
 if source is None:source=(E/'NEW_geometry.rs.txt').read_text()
 base=inherited.check(source)
 fns=functions(source)
 body=fns['NET_reserve_case'][0][1]
 for required in [
  'let k:usize=kani::any();kani::assume(k<N);let len=5*k;let raw:[u32;M]=kani::any();',
  'let p=Box::into_raw(Box::new([core::mem::MaybeUninit::<M31>::uninit();M])) as *mut M31;',
  'let mut dst=unsafe{Vec::from_raw_parts(p,len,M)};',
  'let offset:usize=kani::any();kani::assume(offset<M);if offset<len{assert_eq!(dst[offset].0,raw[offset]);}',
  'dst.reserve(5);',
  'assert_eq!(dst.len(),len);assert_eq!(dst.capacity(),cap);assert_eq!(dst.as_ptr(),p);',
  'if offset<len{assert_eq!(dst[offset].0,raw[offset]);}'
 ]:
  tokens=tok(required)
  assert any(body[i:i+len(tokens)]==tokens for i in range(len(body)-len(tokens)+1)),required
 assert body.count('reserve')==1
 for j in range(60):
  required=f'if {j}<M && {j}<len {{unsafe{{p.add({j}).write(M31(*raw.as_ptr().add({j})));}}}}'
  tokens=tok(required)
  assert any(body[i:i+len(tokens)]==tokens for i in range(len(body)-len(tokens)+1)),required
 assert not any(t in body for t in ['while','for'])
 assert not any(t in source for t in ['static mut','UnsafeCell','Cell<','Atomic','Option<fn','stub_verified','proof_for_contract'])
 return dict(inherited_source_sites=base,source_sha256=hashlib.sha256(source.encode()).hexdigest(),setup='arbitrary live words at variable logical length 5*k; uninitialized spare; fixed guarded setup, no variable-trip setup loop',root_status='OPEN',composed_credit=False)

if __name__=='__main__':print(json.dumps(check(),indent=1))
