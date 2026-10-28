"""New, explicitly restated1.9.0 binding. Never labels itself the old checker."""
from pathlib import Path
import json,re,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028')
Z=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.0/src')
S=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src')
def clean(s):return re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S)
def tokens(s):return re.findall(r'::|=>|[A-Za-z_]\w*|\d+|[^\s]',clean(s))
def body(s,a):
 s=clean(s);start=s.index('{',s.index(a));n=0
 for i in range(start,len(s)):
  n+=(s[i]=='{')-(s[i]=='}')
  if n==0:return s[start:i+1]
 raise ValueError(a)
checks=[];sources={}
def check(p,a,w,after=None):
 s=p.read_text();part=s[s.index(after):] if after else s;v=body(part,a);assert tokens(v)==tokens(w),(str(p),a,v)
 sources[str(p)]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),text=s)
 checks.append(dict(path=str(p),anchor=a,body=v,complete_body_tokens_match=True))
check(Z/'lib.rs','impl<Z> Drop for Zeroizing<Z>','{fn drop(&mut self) {self.0.zeroize();}}')
check(Z/'lib.rs','impl<Z> Zeroize for Z','{fn zeroize(&mut self) {volatile_write(self, Z::default());optimization_barrier(self);}}')
check(Z/'lib.rs','impl<Z, const N: usize> Zeroize for [Z; N]','{fn zeroize(&mut self) {self.iter_mut().zeroize();}}')
check(Z/'lib.rs',"impl<Z> Zeroize for IterMut<'_, Z>",'{fn zeroize(&mut self) {for elem in self {elem.zeroize();}}}')
check(Z/'lib.rs','fn volatile_write<T: Copy + Sized>(dst: &mut T, src: T)','{unsafe {ptr::write_volatile(dst, src)}}')
check(Z/'lib.rs','impl_zeroize_with_default! {','{PhantomPinned, (), bool, char, f32, f64, i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize}')
# Whole barrier body includes both cfg branches. The x86_64/non-miri branch is selected.
check(Z/'barrier.rs','pub fn optimization_barrier<T: ?Sized>', '''{
 #[cfg(all(not(miri),any(target_arch="aarch64",target_arch="arm",target_arch="arm64ec",target_arch="loongarch64",target_arch="riscv32",target_arch="riscv64",target_arch="s390x",target_arch="x86",target_arch="x86_64",)))]
 unsafe {core::arch::asm!("# {}",in(reg) core::ptr::from_ref::<T>(val).cast::<()>(),options(readonly,preserves_flags,nostack),);}
 #[cfg(not(all(not(miri),any(target_arch="aarch64",target_arch="arm",target_arch="arm64ec",target_arch="loongarch64",target_arch="riscv32",target_arch="riscv64",target_arch="s390x",target_arch="x86",target_arch="x86_64",))))]
 {#[inline(never)] fn custom_black_box(p:*const u8){let _=unsafe{core::ptr::read_volatile(p)};}
 core::hint::black_box(val);if size_of_val(val)>0{custom_black_box(core::ptr::from_ref(val).cast::<u8>());}}
}''')
check(S/'default.rs','macro_rules! default_impl','''{($t:ty,$v:expr,$doc:tt)=>{#[stable(feature="rust1",since="1.0.0")] #[rustc_const_unstable(feature="const_default",issue="143894")] impl const Default for $t {#[inline(always)] #[doc=$doc] fn default()->$t{$v}}};}''')
check(S/'default.rs','default_impl! { u8,','{u8,0,"Returns the default value of `0`"}')
check(S/'ptr/non_null.rs','pub const fn cast<U>','{unsafe {NonNull {pointer:self.as_ptr() as *mut U}}}')
check(S/'ptr/mod.rs','pub const fn from_ref<T: PointeeSized>','{r}')
check(S/'slice/mod.rs','pub const fn iter_mut','{IterMut::new(self)}')
check(S/'slice/iter.rs','pub(super) const fn new',"""{let len=slice.len();let ptr:NonNull<T>=NonNull::from_mut(slice).cast();unsafe{let end_or_len=if T::IS_ZST{without_provenance_mut(len)}else{ptr.as_ptr().add(len)};Self{ptr,end_or_len,_marker:PhantomData}}}""",after="impl<'a, T> IterMut<'a, T>")
check(S/'ptr/mod.rs','pub unsafe fn write_volatile<T>',"""{unsafe{ub_checks::assert_unsafe_precondition!(check_language_ub,"ptr::write_volatile requires that the pointer argument is aligned",(addr:*mut ()=dst as *mut (),align:usize=align_of::<T>(),)=>ub_checks::maybe_is_aligned(addr,align));intrinsics::volatile_store(dst,src);}}""")
# Pin the complete next body in the iterator macro (u8 is non-ZST); no mixed/back iterator model.
check(S/'slice/iter/macros.rs','fn next(&mut self) -> Option<$elem>', '''{
 let ptr=self.ptr;let end_or_len=self.end_or_len;
 unsafe {if T::IS_ZST{let len=end_or_len.addr();if len==0{return None;}self.end_or_len=without_provenance_mut(len.unchecked_sub(1));}
 else {if ptr==crate::intrinsics::transmute::<$ptr,NonNull<T>>(end_or_len){return None;}self.ptr=ptr.add(1);}
 Some({ptr}.$into_ref())}
}''')
check(S/'ptr/non_null.rs','pub const fn from_mut','{unsafe {NonNull {pointer:r as *mut T}}}')
check(S/'ptr/non_null.rs','pub const fn as_ptr','{unsafe {mem::transmute::<Self,*mut T>(self)}}')
check(S/'ptr/non_null.rs',"pub const unsafe fn as_mut<'a>",'{unsafe {&mut *self.as_ptr()}}')
check(S/'ptr/non_null.rs','pub const unsafe fn add','{unsafe {NonNull {pointer:intrinsics::offset(self.as_ptr(),count)}}}')
check(S/'ptr/non_null.rs','fn eq(&self, other: &Self)','{self.as_ptr()==other.as_ptr()}')
check(S/'ptr/const_ptr.rs','pub const fn cast<U>','{self as _}')
check(S/'slice/mod.rs','pub const fn len(&self)','{ptr::metadata(self)}')
check(S/'ptr/metadata.rs','pub const fn metadata<T: PointeeSized>','{ptr_metadata(ptr)}')
check(S/'iter/traits/collect.rs','fn into_iter(self) -> I','{self}',after='impl<I: Iterator> IntoIterator for I')
check(S/'iter/traits/iterator.rs','fn next(&mut self) -> Option<I::Item>','{(**self).next()}',after='impl<I: Iterator + ?Sized> Iterator for &mut I')
check(S/'ptr/mut_ptr.rs','pub const unsafe fn add',"""{
 #[cfg(debug_assertions)] #[inline] #[rustc_allow_const_fn_unstable(const_eval_select)]
 const fn runtime_add_nowrap(this:*const (),count:usize,size:usize)->bool {
 const_eval_select!(@capture {this:*const (),count:usize,size:usize}->bool:
 if const {true} else {let Some(byte_offset)=count.checked_mul(size) else {return false;};let (_,overflow)=this.addr().overflowing_add(byte_offset);byte_offset <= (isize::MAX as usize) && !overflow})}
 #[cfg(debug_assertions)] ub_checks::assert_unsafe_precondition!(check_language_ub,"ptr::add requires that the address calculation does not overflow",(this:*const ()=self as *const (),count:usize=count,size:usize=size_of::<T>(),)=>runtime_add_nowrap(this,count,size));
 unsafe {intrinsics::offset(self,count)}
}""")
(D/'zeroize190-complete-structural.json').write_text(json.dumps(dict(evidence_class='structural (K-1 substitute)',checks=checks,sources=sources,selected_cfg=dict(target_arch='x86_64',miri=False),before='volatileWrite(addr,0); compilerFence(SeqCst)',after='volatileWrite(addr,0); asmReadBarrier(addr), readonly/preserves_flags/nostack; neither pure nor nomem',law='PV_RDCD_ZeroWorld and ZeroTrace; emitted dictionaries ZeroSelected; std cursor correspondence ZeroCursor',primitive_boundary='valid exclusive u8 array; Rust pointer casts preserve address and validity, u8 size/alignment1; pointer addition stays within array or one-past; write_volatile primitive; no concurrent aliases',excluded='No CPU fence, synchronization, register/spill/copy erasure, allocator clearing or L3 emitted-binary audit',d188='No iterator Aeneas emission credited; owned recursion retains every changed byte'),indent=2)+'\n');print('PASS revised complete zeroize1.9.0 bodies and selected std bodies')
