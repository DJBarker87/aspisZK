"""Full native update/buffer/split bodies checked against the owned index body."""
from pathlib import Path
import subprocess,json,re,hashlib
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
r=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f');b=Path('/home/dombarker/project-offloads/codex-pv-dlib-20261028/native');out={}
for n in ['digest-0.10.7/src/core_api/wrapper.rs','block-buffer-0.10.4/src/lib.rs','block-buffer-0.10.4/src/sealed.rs']:
 p=r/n;s=p.read_bytes();assert (b/n).read_bytes().startswith(s)
 out[n]=dict(path=str(p),sha256=hashlib.sha256(s).hexdigest(),source=p.read_text())
print(json.dumps(out))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
files=json.loads(r.stdout);w=files['digest-0.10.7/src/core_api/wrapper.rs']['source'];b=files['block-buffer-0.10.4/src/lib.rs']['source'];s=files['block-buffer-0.10.4/src/sealed.rs']['source'];eager=s[s.index('impl Sealed for super::Eager'):s.index('impl Sealed for super::Lazy')]
native=dict(wrapper=body(w[w.index('impl<T> Update for'):],'fn update'),buffer=body(b,'pub fn digest_blocks'),invariant=body(eager,'fn invariant'),split=body(eager,'fn split_blocks'))
expected=dict(wrapper='''{let Self{core,buffer}=self;buffer.digest_blocks(input,|blocks|core.update_blocks(blocks));}''',buffer='''{let pos=self.get_pos();let rem=self.size()-pos;let n=input.len();
if Kind::invariant(n,rem) {self.buffer[pos..][..n].copy_from_slice(input);self.set_pos_unchecked(pos+n);return;}
if pos!=0 {let(left,right)=input.split_at(rem);input=right;self.buffer[pos..].copy_from_slice(left);compress(slice::from_ref(&self.buffer));}
let(blocks,leftover)=Kind::split_blocks(input);if !blocks.is_empty(){compress(blocks);}
let n=leftover.len();self.buffer[..n].copy_from_slice(leftover);self.set_pos_unchecked(n);}''',invariant='{pos<block_size}',split='''{let nb=data.len()/N::USIZE;let blocks_len=nb*N::USIZE;let tail_len=data.len()-blocks_len;unsafe{let blocks_ptr=data.as_ptr() as *const Block<N>;let tail_ptr=data.as_ptr().add(blocks_len);(slice::from_raw_parts(blocks_ptr,nb),slice::from_raw_parts(tail_ptr,tail_len),)}}''')
for key in native:assert tokens(native[key])==tokens(expected[key]),key
p=R/'tools/pv-dlib-20261028/default-reference.rs';owned=body(p.read_text(),'pub fn update_batch_reference')
expected_owned='''{let n=input.len();let rem=64-pos;if n<rem {let mut i=0;while i<n {buffer[pos+i]=input[i];i+=1;}return(state,buffer,pos+n);}
let mut start=0;if pos!=0 {let mut i=0;while i<rem {buffer[pos+i]=input[i];i+=1;}state=C::compress(state,&buffer);start=rem;}
let full=(n-start)/64;let end=start+full*64;if full!=0 {state=C::compress(state,&input[start..end]);}
let left=n-end;let mut j=0;while j<left {buffer[j]=input[end+j];j+=1;}(state,buffer,left)}'''
assert tokens(owned)==tokens(expected_owned)
out=dict(row='V236',evidence_class='structural (K-1 substitute)',rulings=['r',"k'"],sources={n:{k:v for k,v in d.items() if k!='source'} for n,d in files.items()},native_bodies=native,owned_reference=dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),body=owned,whole_body_token_checked=True),differences=[dict(native='borrowed core/buffer, slice copy',reference='owned state/buffer and element cursor copy',proof='UpdateCopy.copy/cells_value/bounds; UpdatePlan.shape; StorageIdentity.rebuild; all retained bytes preserved'),dict(native='first input split_at(rem), then Eager split_blocks of remaining bytes',reference='start/end index arithmetic and one whole bulk callback',proof='UpdatePlan.source_reference, BatchPlan.reassemble/remainder, UpdateViews.native_bulk/coordinate/byte/native_block_lengths; same V233 take/drop quotient specification, no suspended copy-dependent Kani credit'),dict(native='compress receives borrowed sequence of native64-byte blocks',reference='compress receives the same contiguous bytes, exact call boundaries',proof='UpdateViews.count/joined/native_bulk; UpdateCarrier.decoded_blocks/compression_call; UpdatePlan.complete for arbitrary batched Result callback; no singleton-fold premise introduced')],guard='Original SHA-cohort Eager64 safe private pos<64, native byte-slice size bound; generated Eager dictionary selected by UpdateSelected.native_kind/bufferKind and retained_kind (not by erased Unit marker type); native size discharged by native_size; no guard changed. All checked subtraction/range paths discharged symbolically.',complete_result='PV_DL_UpdatePlan.complete',finite_validation='../wrappers-native-combined-resume4/receipt.json',finite_scope='99328 paired same-input native/reference cases; exact batch boundaries and bytes, counter including wrap, all retained64buffer bytes and cursor; finite validation only',compression='arbitrary Result-valued batched callback, no backend/V232 equality assumed',v232_untouched=True,kani=False)
(E/'V236/structural-binding.json').write_text(json.dumps(out,indent=2)+'\n');print('Full native update, Eager invariant/split and owned index bodies checked')
