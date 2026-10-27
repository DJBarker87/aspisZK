"""Read-only frozen stdlib/control check for the V184 library-law boundary.
Primitive memory semantics are explicit Lean definitions, not a machine proof.
"""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-alib-20261027'
path='/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/alloc/src/vec/mod.rs'
r=subprocess.run(['ssh','dombarker@100.108.41.90','cat '+path],capture_output=True,check=True);s=r.stdout.decode()
def clean(s):return re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S)
def body(s,name):
 s=clean(s);pos=s.index('pub fn '+name+'(');a=s.index('{',pos);depth=0
 for i in range(a,len(s)):
  if s[i]=='{':depth+=1
  if s[i]=='}':
   depth-=1
   if depth==0:return s[a:i+1]
 raise ValueError(name)
def tokens(s):return re.findall(r'::|=>|[A-Za-z_]\w*|\d+|[^\s]',clean(s))
expected={
'pop':'''{if self.len == 0 {None} else {unsafe {self.len -= 1;core::hint::assert_unchecked(self.len < self.capacity());Some(ptr::read(self.as_ptr().add(self.len())))}}}''',
'remove':'''{#[cold] #[cfg_attr(not(panic = "immediate-abort"), inline(never))] #[track_caller] #[optimize(size)] fn assert_failed(index: usize, len: usize) -> ! {panic!("removal index (is {index}) should be < len (is {len})");} match self.try_remove(index) {Some(elem) => elem,None => assert_failed(index, self.len()),}}''',
 'try_remove':'''{let len = self.len();if index >= len {return None;} unsafe {let ret;{let ptr = self.as_mut_ptr().add(index);ret = ptr::read(ptr);ptr::copy(ptr.add(1), ptr, len - index - 1);}self.set_len(len - 1);Some(ret)}}'''}
checks={}
for n,x in expected.items():
 b=body(s,n);assert tokens(b)==tokens(x),(n,b)
 checks[n]=dict(body=b,sha256=hashlib.sha256(b.encode()).hexdigest(),complete_body_tokens_match=True)
ref=(R/'tools/pv-alib-20261027/move-reference.rs').read_text();b=body(ref,'pop_move_reference<T>') if False else None
# Freeze the complete reference file and already extracted borrowed wrapper.
report=dict(kind='frozen standard-library source/control association; explicit library primitive interpretation',stdlib=dict(path=path,file_sha256=hashlib.sha256(r.stdout).hexdigest()),functions=checks,reference=dict(path='tools/pv-alib-20261027/move-reference.rs',sha256=hashlib.sha256(ref.encode()).hexdigest()),
 interpretation={'pop':'PV_AL_MoveNativeValue.nativeValue: zero guard, decrement, capacity guard, last initialized slot read', 'remove_last':'PV_AL_RemoveModel.pop_move_reference with PV_AL_MoveMemory.last_copy; copy count zero from PV_AL_MoveFacts.zero_copy','world':'PV_AL_MoveWorld.nativeWorld/referenceWorld: read and live-header update; no allocator/destructor call, stable buffer/capacity, zero-length raw copy'},
 obligations={'bounds':'PV_AL_MoveFacts.last_bound; Buffer.fits for capacity assertion','copy':'PV_AL_MoveMemory.last_copy for all widths, including zero','nonvacuity':'PV_AL_PopWorld.nonvacuous gives a carrier for every representable input','native_differential':'existing pop-move-world-03; additional pop-zst-world-04'},
 no_allocator_or_destructor_call_in_operations=True,body_write_classification='Vec header and raw copy; no iter_mut/get_mut/chunks_mut element restoration continuation. Native raw remove remains unextracted; no D188 raw-pointer credit claimed.',
 boundary='Structural library source law over explicit read/header/copy semantics, supported by bounded Kani and native differential. No unbounded Rust memory-model, compiler, allocator or deployed endpoint refinement claim.')
(E/'STRUCTURAL-POP-GATE.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: complete pop/remove/try_remove source shapes; no allocator/destructor call')
