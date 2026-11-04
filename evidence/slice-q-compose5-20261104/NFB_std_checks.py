"""Pinned std resize source audit, separate from binary/library trust."""
from pathlib import Path
import hashlib,json,re
from NFB_source_checks import tok
E=Path(__file__).resolve().parent

def check(vec=None,guard=None):
 vec=(E/'NFB_STD_alloc_vec_mod.rs.txt').read_text() if vec is None else vec
 guard=(E/'NFB_STD_alloc_vec_set_len_on_drop.rs.txt').read_text() if guard is None else guard
 def has(s,text):
  s=re.sub(r'/\*.*?\*/','',s,flags=re.S);s=re.sub(r'//[^\n]*','',s)
  a,b=tok(s),tok(text)
  assert any(a[i:i+len(b)]==b for i in range(len(a)-len(b)+1)),text
 has(vec,'pub fn resize(&mut self,new_len:usize,value:T){let len=self.len();if new_len>len{self.extend_with(new_len-len,value)}else{self.truncate(new_len);}}')
 for text in ['self.reserve(n);','let mut ptr=self.as_mut_ptr().add(self.len());','let mut local_len=SetLenOnDrop::new(&mut self.len);','for _ in 1..n {ptr::write(ptr,value.clone());ptr=ptr.add(1);local_len.increment_len(1);}','if n>0 {ptr::write(ptr,value);local_len.increment_len(1);}']:
  has(vec, text if not text.startswith('for ') else text)
 has(guard,'pub(super) fn new(len:&\'a mut usize)->Self{SetLenOnDrop{local_len:*len,len}}')
 has(guard,'pub(super) fn increment_len(&mut self,increment:usize){self.local_len+=increment;}')
 has(guard,'fn drop(&mut self){*self.len=self.local_len;}')
 return dict(commit='53732d5e0',vec_sha256=hashlib.sha256(vec.encode()).hexdigest(),set_len_sha256=hashlib.sha256(guard.encode()).hexdigest(),native_iteration='NFB_K033/NFB_K037 and controls: one actual Vec::resize append, from arbitrary live pre-state',clone_obligation='M31 derived Copy clone identity; same value and no effects',induction='NFB_ResizeTrace.complete',qualification='Upstream pinned compiler source; installed compiler/library objects independently pinned, no assertion of source-reproducible std build')
if __name__=='__main__':print(json.dumps(check(),indent=1))
