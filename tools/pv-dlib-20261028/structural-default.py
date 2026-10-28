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
import hashlib,json
r=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f');b=Path('/home/dombarker/project-offloads/codex-pv-dlib-20261028/native');out={}
for n in ['digest-0.10.7/src/core_api/wrapper.rs','block-buffer-0.10.4/src/lib.rs','generic-array-0.14.7/src/impls.rs']:
 p=r/n;s=p.read_bytes();out[n]=dict(path=str(p),sha256=hashlib.sha256(s).hexdigest(),source=p.read_text())
 if not n.startswith('generic-array'):assert (b/n).read_bytes().startswith(s),n
print(json.dumps(out))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
files=json.loads(r.stdout);w=files['digest-0.10.7/src/core_api/wrapper.rs']['source'];b=files['block-buffer-0.10.4/src/lib.rs']['source']
assert re.search(r'#\[derive\(Clone,\s*Default\)\]\s*pub struct CoreWrapper',w)
assert tokens(body(w,'pub struct CoreWrapper'))==tokens('{core:T,buffer:BlockBuffer<T::BlockSize,T::BufferKind>,}')
default=body(b,'fn default()')
expected='''{if BlockSize::USIZE==0 {panic!("Block size can not be equal to zero");}
 Self {buffer:Default::default(),pos:0,_pd:PhantomData,}}'''
assert tokens(default)==tokens(expected),default
assert tokens(body(files['generic-array-0.14.7/src/impls.rs']['source'],'fn default()'))==tokens('{Self::generate(|_|T::default())}')
p=R/'tools/pv-dlib-20261028/default-forward-helper.rs';owned=body(p.read_text(),'pub fn pv_dl_owned_default')
assert tokens(owned)==tokens('{Self{core:Default::default(),buffer:Default::default()}}')
j=dict(evidence_class='structural (K-1 substitute)',rulings=['r',"k'"],sources={n:{k:v for k,v in a.items() if k!='source'} for n,a in files.items()},
 wrapper_fields='core:T then buffer:Buffer<T>; native derives Default in declaration order',native_buffer_default=default,
 owned_reference=dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),body=owned,tokens_checked=True),
 differences=[dict(native='derived CoreWrapper Default',reference='explicit same two field-default calls in declaration order',proofs=['PV_DL_DefaultLaw.source','PV_DL_WrapLaw.source_reference']),
 dict(native='BlockBuffer default checks size0 then byte-array Default,pos0,PhantomData',reference='native64-byte storage constructor',proofs=['PV_DL_DefaultNative.native_callback','PV_DL_DefaultNative.consumed','PV_DL_DefaultBuffer.nonvacuous'])],
 native_size='64, discharged by PV_AL_SplitNativeShape.native_size; core Default is an original complete-Result parameter; kind/size Default trait arguments are not executed by these fields',
 finite_validation='default-native-finite-resume/receipt.json required before credit; native finite validation only',
 old_kani_credit='suspended; not used',v232_untouched=True,kani=False)
(E/'V237/structural-binding.json').write_text(json.dumps(j,indent=2)+'\n');print('derived field order and full native/default buffer bodies checked')
