from pathlib import Path
import json,lzma,hashlib,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2c-20261028');OLD=D.parent/'codex-pv-rdb2-20261028'
files=json.loads(lzma.decompress((OLD/'prior-sources.json.xz').read_bytes()))['files'];checks=[]
def tokens(s):
 s=re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S)
 return re.findall(r'"(?:[^"\\]|\\.)*"|::|=>|\w+|[^\s]',s)
def body(s,needle):
 a=s.index('{',s.index(needle));depth=0
 for i in range(a,len(s)):
  depth+=(s[i]=='{')-(s[i]=='}')
  if depth==0:return s[a:i+1]
def get(k):
 j=files[k];s=j['text'];assert hashlib.sha256(s.encode()).hexdigest()==j['sha256']
 if k.startswith('deployed/'):assert hashlib.sha256(Path(j['path']).read_bytes()).hexdigest()==j['sha256']
 return s
for cohort in ['evidence','deployed']:
 k=cohort+'/library/alloc/src/raw_vec/mod.rs';s=get(k);b=body(s,'fn new_in(alloc: A)')
 expected='''{const { assert!(T::LAYOUT.size() % T::LAYOUT.align() == 0) }; Self { inner: RawVecInner::new_in(alloc, Alignment::of::<T>()), _marker: PhantomData }}'''
 assert tokens(b)==tokens(expected),(cohort,b)
 checks.append(dict(family='typed RawVec<T,A>::new_in',cohort=cohort,body=b,source_sha256=files[k]['sha256'],proof='R1Z.PV_RDB2C_TypedRawVec.complete; no_allocation; zst_capacity; non_zst_capacity',calls=['RawVecInner::new_in(alloc, Alignment::of::<T>())'],allocations=[],marker='PhantomData has no runtime contents',constant_assertion='Rust real-type layout padded to its alignment; compile-time assertion, no runtime allocation'))
for cohort in ['evidence','deployed']:
 k=cohort+'/library/alloc/src/boxed.rs';s=get(k);b=body(s,'pub fn new(x: T)')
 expected = ('{let ptr=box_new_uninit(<T as SizedTypeProperties>::LAYOUT) as *mut T;unsafe {core::intrinsics::write_via_move(ptr,x)};unsafe {mem::transmute(ptr)}}' if cohort=='evidence' else '{return box_new(x);}')
 assert tokens(b)==tokens(expected),(cohort,b)
 checks.append(dict(family='Box::new',cohort=cohort,source_sha256=files[k]['sha256'],body=b,calls=(['box_new_uninit(Layout::new::<T>())','write_via_move(ptr,x)','transmute(ptr)'] if cohort=='evidence' else ['box_new(x)']),intrinsic_lowering='NOT inferred from this source body; requires pinned compiler MIR association',proof='R1Z.PV_RDB2C_Box.complete applies only once lowering is associated'))
pins=json.loads((D/'project-pins.json').read_text());S=OLD/'src'
for p,h in pins.items():
 raw=(S/p).read_bytes();assert hashlib.sha256(raw).hexdigest()==h
 checks.append(dict(family='frozen project source',path=p,sha256=h))
w=(S/'crates/aspis-r1-cost-probe/src/weights.rs').read_text()
assert tokens(body(w,'pub fn materialize('))==tokens('''{let kp=powers::<7>(kappa);let mut w=match aspis_core::r0::heap::filled(1024,E::ZERO){Ok(v)=>v,Err(_)=>return Err(Error::Allocation)};for (j,v) in w.iter_mut().enumerate(){for kind in 0..7 {*v=v.add(kp[kind].mul_qm31(self.raw(kind,j)));}}Ok(w)}''')
assert tokens(body(w,'fn box_from_parts('))==tokens('{Box::new(Self {variant,factors,points,extra})}')
heap=(S/'crates/aspis-core/src/r0/heap.rs').read_text()
assert tokens(body(heap,'pub fn filled<T: Copy>'))==tokens('{let mut out=Vec::new();out.try_reserve_exact(n).map_err(|_|Error::Allocation)?;out.resize(n,value);Ok(out)}')
checks.append(dict(family='V258 allocation path',public_n=1024,element='WideExact',order=['powers7 (stack only)','Vec::new (no request)','try_reserve_exact(1024)','on failure return Error::Allocation before resize/iteration','resize(1024, WideExact::ZERO)','mutable iteration'],request_count='one nonzero request; resize fits exact reserved capacity; no realloc; early allocation failure retains private allocator post-state',public_factorization='literal 1024 * size_of::<WideExact>(), align_of::<WideExact>(); order independent of self and kappa',remaining='complete emitted/owned materialize mutable continuation and concrete arithmetic association'))
checks.append(dict(family='V259 allocation path',order=['pure fixed-array constructor arithmetic','box_from_parts','Box::new'],public_factorization='one Layout::new::<Weights>(), independent of values; no realloc',failure='allocation abort, not Error::Allocation; no returning initialized box on failure',remaining='pinned compiler intrinsic lowering and complete constructor source/callback association'))
j=dict(checks=checks,toolchain='1.94.1',configuration='associated deployed features/profile in project-pins configuration receipt; no Rust compile in this scope',restored=[],trust='reclassification within existing tool trust, not premise removal; runtime/allocator primitive adequacy retained by name')
(D/'alloc-binding.json').write_text(json.dumps(j,indent=2));print(json.dumps(j,indent=2))
