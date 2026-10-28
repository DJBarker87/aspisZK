from pathlib import Path
import json,re,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028')
def sha(b):return hashlib.sha256(b).hexdigest()
def toks(s):return re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]',re.sub(r'//[^\n]*|/\*.*?\*/','',s,flags=re.S))
def fn(s,marker):
 assert s.count(marker)==1,(marker,s.count(marker))
 a=s.index(marker);b=s.index('{',a);e=b+1;depth=1
 while depth:depth+=(s[e]=='{')-(s[e]=='}');e+=1
 return s[a:e],s[b:e]
plan=[('core/src/mem/mod.rs','pub const fn take<T: [const] Default>(dest: &mut T) -> T','take'),('core/src/mem/mod.rs','pub const fn replace<T>(dest: &mut T, src: T) -> T','replace'),('alloc/src/vec/mod.rs','fn default() -> Vec<T>','Vec.default'),('alloc/src/vec/mod.rs','pub const fn new() -> Self','Vec.new'),('alloc/src/raw_vec/mod.rs','pub(crate) const fn new() -> Self','RawVec.new'),('alloc/src/raw_vec/mod.rs','pub(crate) const fn new_in(alloc: A) -> Self','RawVec.new_in'),('alloc/src/raw_vec/mod.rs','const fn new_in(alloc: A, align: Alignment) -> Self','RawVecInner.new_in'),('core/src/ptr/non_null.rs','pub const fn without_provenance(addr: NonZero<usize>) -> Self','NonNull.without_provenance'),('core/src/ptr/unique.rs','pub const fn from_non_null(pointer: NonNull<T>) -> Self','Unique.from_non_null'),('core/src/ptr/alignment.rs','pub const fn of<T>() -> Self','Alignment.of'),('core/src/ptr/alignment.rs','pub const fn as_nonzero(self) -> NonZero<usize>','Alignment.as_nonzero')]
cohorts=[]
for version in ['nightly-2026-06-01','1.94.1']:
 R=Path('/home/dombarker/.rustup/toolchains')/(version+'-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library');rec=dict(version=version,files={},bodies={})
 for f,marker,key in plan:
  actual=f.replace('core/src/ptr/alignment.rs','core/src/mem/alignment.rs') if version=='nightly-2026-06-01' else f
  q=R/actual;s=q.read_text();whole,b=fn(s,marker);rec['files'][f]=dict(path=str(q),sha256=sha(q.read_bytes()));rec['bodies'][key]=dict(text=whole,body_token_sha256=sha('\0'.join(toks(b)).encode()))
 q=R/'core/src/array/mod.rs';s=q.read_text();whole,b=fn(s,'macro_rules! array_impl_default');rec['files']['core/src/array/mod.rs']=dict(path=str(q),sha256=sha(q.read_bytes()));rec['bodies']['arrayDefault_macro']=dict(text=whole,body_token_sha256=sha('\0'.join(toks(b)).encode()));assert 'array_impl_default! {32,' in s
 cohorts.append(rec)
R=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
deployed_extra=[]
for f,marker,key in [('core/src/ptr/alignment.rs','pub const fn new(align: usize) -> Option<Self>','Alignment.new'),('core/src/ptr/alignment.rs','pub const unsafe fn new_unchecked(align: usize) -> Self','Alignment.new_unchecked'),('core/src/ptr/mod.rs','pub const fn without_provenance<T>(addr: usize) -> *const T','ptr.without_provenance'),('core/src/num/nonzero.rs','pub const fn get(self) -> T','NonZero.get'),('core/src/num/uint_macros.rs','pub const fn is_power_of_two(self) -> bool','usize.is_power_of_two'),('core/src/num/uint_macros.rs','pub const fn count_ones(self) -> u32','usize.count_ones')]:
 q=R/f;text=q.read_text();whole,b=fn(text,marker);deployed_extra.append(dict(name=key,path=str(q),file_sha256=sha(q.read_bytes()),body=whole,body_token_sha256=sha('\0'.join(toks(b)).encode())))
alignment=(R/'core/src/ptr/alignment.rs').read_text()
assert '#[repr(transparent)]' in alignment and '#[repr(usize)]' in alignment
# The two concrete source types are ordinary four-u32/two-u32 compositions;
# their deployed compiler layouts are independently checked in the native gate.
source_laws=dict(metadata_frame='R1Z.PV_RDCD_EmptyRaw194.raw_valid/raw_four',alignment_validation='R1Z.PV_RDCD_EmptyRaw194.power_four/alignment_valid',zero_length_projection='R1Z.PV_RDCD_EmptyRaw194.zero_length_view',array_defaults='R1Z.PV_RDCD_Defaults194.array_values',concrete_takes='R1Z.PV_RDCD_TakeBinding.vector_m31/vector_qm31/array10/array16',Rust_primitive_boundary='address-preserving valid transmute/without_provenance, ctpop, typed layout and scalar loads/moves; no native machine/world composition claimed')
identity={k:cohorts[0]['bodies'][k]['body_token_sha256']==cohorts[1]['bodies'][k]['body_token_sha256'] for k in cohorts[0]['bodies']}
record=dict(row='V169',cohorts=cohorts,deployed_extra_bodies=deployed_extra,deployed_source_laws=source_laws,body_identity=identity,concrete_defaults=['Vec<M31>','Vec<QM31>','[Vec<M31>;10]','[Vec<M31>;16]'],law='PV_RDCD_Defaults194: Vec.new empty value and left-to-right array literal defaults; fresh generic take returns old value and replacement',primitive_boundary='layout/align/NonZero, pointer address/without-provenance constructors and ownership-preserving read/write moves; native carrier/world composition and L1/L2/L3 retained',qualification='Source-body census and selected instantiation law binding; never labelled a recovered original structural checker. The original extraction route is separately replayed.')
(D/'resume-v169-original-route/source-binding.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(identity,indent=2))
