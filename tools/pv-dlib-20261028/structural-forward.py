"""Native Digest and CoreWrapper forwarding source binding, no Kani."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-dlib-20261028'
row=sys.argv[1];assert row in ['V234','V235']
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
import hashlib,json,tarfile
r=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f');b=Path('/home/dombarker/project-offloads/codex-pv-dlib-20261028/native');out={}
for n in ['digest-0.10.7/src/digest.rs','digest-0.10.7/src/lib.rs','digest-0.10.7/src/core_api/wrapper.rs','generic-array-0.14.7/src/impls.rs']:
 p=r/n;s=p.read_bytes();out[n]=dict(path=str(p),sha256=hashlib.sha256(s).hexdigest(),source=p.read_text())
 if n.startswith('digest-'):assert (b/n).read_bytes().startswith(s),n
p=Path('/home/dombarker/.cargo/registry/cache/index.crates.io-1949cf8c6b5b557f/generic-array-0.14.7.crate')
assert hashlib.sha256(p.read_bytes()).hexdigest()=='85649ca51fd72272d7821adaf274ad91c288277713d9c18820d8499a7ff69e9a'
count=0
with tarfile.open(p) as archive:
 for member in archive.getmembers():
  if member.isfile():
   assert (r/member.name).read_bytes()==archive.extractfile(member).read(),member.name
   count+=1
print(json.dumps(dict(files=out,generic_array_all_checksum_files_verified=count)))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
j=json.loads(r.stdout);files=j['files'];src=files['digest-0.10.7/src/digest.rs']['source'];impl=src[src.index('impl<D:'):]
digest=body(impl,'fn finalize(self)');assert tokens(digest)==tokens('{FixedOutput::finalize_fixed(self)}')
fixed=body(files['digest-0.10.7/src/lib.rs']['source'],'fn finalize_fixed(self)')
assert tokens(fixed)==tokens('{let mut out=Default::default();self.finalize_into(&mut out);out}')
w=files['digest-0.10.7/src/core_api/wrapper.rs']['source'];wrapper=body(w,'impl<T> FixedOutput for CoreWrapper<T>')
assert re.findall(r'\bfn (\w+)\(',wrapper)==['finalize_into'],'CoreWrapper has finalize_fixed override'
forward=body(wrapper,'fn finalize_into')
assert tokens(forward)==tokens('{let Self{core,buffer}=&mut self;core.finalize_fixed_core(buffer,out);}')
decompose=body(w,'pub fn decompose')
assert tokens(decompose)==tokens('{let Self{core,buffer}=self;(core,buffer)}')
gadefault=body(files['generic-array-0.14.7/src/impls.rs']['source'],'fn default()')
assert tokens(gadefault)==tokens('{Self::generate(|_|T::default())}')
p=R/'tools/pv-dlib-20261028/digest-forward-native.rs';s=p.read_text()
assert tokens(body(s,'fn owned_digest'))==tokens('{FixedOutput::finalize_fixed(d)}')
assert tokens(body(s,'fn default_fixed'))==tokens('{let mut out=Default::default();FixedOutput::finalize_into(d,&mut out);out}')
assert tokens(body(s,'fn owned_fixed'))==tokens('{d.pv_dl_owned_finalize_into(out);}')
helper=R/'tools/pv-dlib-20261028/fixed-forward-helper.rs'
assert tokens(body(helper.read_text(),'pub fn pv_dl_owned_finalize_into'))==tokens(forward),'owned core wrapper body differs'
out=dict(row=row,evidence_class='structural (K-1 substitute)',rulings=['r',"k'"],
 sources={n:{k:v for k,v in a.items() if k!='source'} for n,a in files.items()},
 generic_array_all_checksum_files_verified=j['generic_array_all_checksum_files_verified'],
 native_bodies=dict(blanket_digest=digest,fixed_default=fixed,core_wrapper=forward,decompose=decompose,array_default=gadefault),
 owned_reference=dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),three_complete_bodies_token_checked=True,owned_fixed_helper=str(helper.relative_to(R)),helper_sha256=hashlib.sha256(helper.read_bytes()).hexdigest()),
 dispatch_scope='Generic Digest forwarding preserves finalize_fixed overrides; default expansion is tied to shipped CoreWrapper impl, which has no override. Typed installation is the frozen32-byte output carrier.',
 differences=[dict(native='method call syntax and receiver self',reference='UFCS call syntax and receiver d',proof='PV_DL_DigestFinal.complete; same method dispatch by full token binding'),
 dict(native='FixedOutput default initializes GenericArray then consumes self in finalize_into',reference='same initialization and consuming callback order',proof='PV_DL_DigestFinal.reference; original complete-Result callback retained, including its destructor behavior'),
 dict(native='borrow fields in consumed wrapper',reference='identical consumed-self field borrows and core call in owned helper; same implicit destructor',proof='PV_DL_OwnershipEffects.complete_result (V235); complete world is retained on callback failure and destructor sees changed state')],
 finite_validation='digest-forward-native-finite-resume/receipt.json; required before credit; finite validation only',
 compression='forwarding preserves original core callback parameters; no compression evaluation law or backend equality assumed',
 v232_untouched=True,kani=False)
if row=='V234':out['differences']=out['differences'][:2]
else:out['differences']=out['differences'][2:]
(E/row/'structural-binding.json').write_text(json.dumps(out,indent=2)+'\n');print(row,'three complete forwarding source bodies, native dispatch and private-prefix checks passed')
