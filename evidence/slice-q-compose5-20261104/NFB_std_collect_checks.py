"""Pin the exact standard-library specialization used by the root collector."""
from pathlib import Path
import re,hashlib,json
from NFB_source_checks import tok,body
E=Path(__file__).resolve().parent
FILES=['alloc_vec_mod','alloc_vec_set_len_on_drop','alloc_vec_spec_from_iter','alloc_vec_spec_from_iter_nested','alloc_vec_spec_extend','core_array_mod','core_iter_map','core_iter_range','alloc_vec_in_place_collect']
def check(texts=None,source=None):
 texts={n:(E/('NFB_STD_'+n+'.rs.txt')).read_text() for n in FILES} if texts is None else texts
 source=(E/'NFB_geometry.rs.txt').read_text() if source is None else source
 def has(n,s):
  t=re.sub(r'/\*.*?\*/','',texts[n],flags=re.S);t=re.sub(r'//[^\n]*','',t)
  a,b=tok(t),tok(s);assert any(a[i:i+len(b)]==b for i in range(len(a)-len(b)+1)),(n,s)
 has('alloc_vec_mod','ptr::write(ptr.add(local_len.current_len()),element);local_len.increment_len(1);')
 has('alloc_vec_spec_from_iter','SpecFromIterNested::from_iter(iterator)')
 has('alloc_vec_spec_from_iter_nested','(_, Some(upper)) => Vec::with_capacity(upper),')
 has('alloc_vec_spec_from_iter_nested','vector.spec_extend(iterator);vector')
 has('alloc_vec_spec_extend','self.extend_trusted(iterator)')
 has('alloc_vec_set_len_on_drop','fn drop(&mut self){*self.len=self.local_len;}')
 has('core_array_mod','self.array_mut.get_unchecked_mut(self.initialized).write(item);self.initialized=self.initialized.unchecked_add(1);')
 has('core_array_mod','let item=generator(guard.initialized).branch()?;')
 has('core_array_mod','unsafe {MaybeUninit::array_assume_init(array)}')
 has('core_iter_map','unsafe impl<B,I,F> TrustedLen for Map<I,F> where I:TrustedLen,F:FnMut(I::Item)->B,{}')
 has('core_iter_map','unsafe impl<I,F> SourceIter for Map<I,F> where I:SourceIter,{type Source=I::Source;')
 has('core_iter_range','unsafe impl<A:TrustedStep> TrustedLen for ops::Range<A> {}')
 has('core_iter_range','unsafe_impl_trusted_step![AsciiChar char i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize Ipv4Addr Ipv6Addr];')
 has('alloc_vec_in_place_collect','trait InPlaceCollect:SourceIter<Source:AsVecIntoIter>+InPlaceIterable{type Src;}')
 assert 'SourceIter' not in texts['core_iter_range']
 assert tok(body(source,'NFB_collect_store'))==tok('unsafe{core::ptr::write(ptr.add(*local_len),element);}*local_len+=1;')
 assert tok(body(source,'NFB_array_store'))==tok('unsafe{data.get_unchecked_mut(*initialized).write(item);*initialized=initialized.unchecked_add(1);}')
 return dict(source_commit='53732d5e0',hashes={n:hashlib.sha256(t.encode()).hexdigest() for n,t in texts.items()},qualified_std_binary_trust=True,publication='guard-local initialized length, then SetLenOnDrop; no premature Vec.len update',array='one guard slot, then exact initialized five-element transfer',dispatch_obligation='Map<Range<usize>,closure> TrustedLen; no in-place Vec iterator input')
if __name__=='__main__':print(json.dumps(check(),indent=1))
