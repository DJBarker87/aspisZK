from pathlib import Path
import re,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028');cohorts=[]
def sha(b):return hashlib.sha256(b).hexdigest()
def toks(s):return re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]',re.sub(r'//[^\n]*|/\*.*?\*/','',s,flags=re.S))
def span(s,marker):
 assert s.count(marker)==1,(marker,s.count(marker))
 a=s.index(marker);b=s.index('{',a);e=b+1;depth=1
 while depth:depth+=(s[e]=='{')-(s[e]=='}');e+=1
 return s[a:e]
for v in ['nightly-2026-06-01','1.94.1']:
 root=Path('/home/dombarker/.rustup/toolchains')/(v+'-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src');rec=dict(toolchain=v,files={},bodies={})
 for f in ['array/equality.rs','cmp/bytewise.rs','intrinsics/mod.rs']:
  p=root/f;s=p.read_text();rec['files'][f]=dict(path=str(p),sha256=sha(p.read_bytes()))
  if f=='array/equality.rs':
   # Typed [u8;32] selects BytewiseEq specialization, never generic slice eq.
   segments={'array_partial_eq':s.split('impl<T, U, const N: usize>',1)[1].split('#[stable',1)[0],
    'bytewise_specialization':s.split('impl<T: [const] BytewiseEq<U>, U, const N: usize>',1)[1]}
   for name,seg in segments.items():
    marker='fn eq(&self, other: &[U; N]) -> bool' if name=='array_partial_eq' else 'fn spec_eq(a: &[T; N], b: &[U; N]) -> bool'
    b=span(seg,marker);rec['bodies'][name]=dict(text=b,token_sha256=sha('\0'.join(toks(b)).encode()))
  elif f=='cmp/bytewise.rs':
   assert re.search(r'\bunsigned\b|\bu8\b',s)
   rec['bodies']['BytewiseEq_trait_and_all_impls']=dict(text=s,token_sha256=sha('\0'.join(toks(s)).encode()))
  else:
   marker='pub const unsafe fn raw_eq<T>'
   a=s.index(marker);e=s.index(';',a)+1;b=s[a:e];rec['bodies']['raw_eq_intrinsic_declaration']=dict(text=b,token_sha256=sha('\0'.join(toks(b)).encode()))
 cohorts.append(rec)
identity={k:cohorts[0]['bodies'][k]['token_sha256']==cohorts[1]['bodies'][k]['token_sha256'] for k in cohorts[0]['bodies']}
assert all(identity.values()),identity
out=dict(row='V216',cohorts=cohorts,identity=identity,instantiation='u8,u8,N=32; BytewiseEq<u8> from exact identical macro impl file; two arrays only',source_cone=['derived context eq','u64 primitive equality','[u8;32] PartialEq::eq','u8 SpecArrayEq::spec_eq','raw_eq and transmute compiler primitives'],excluded_branch='Generic slice equality is not selected for u8; no claim that slice/cmp.rs bodies are unchanged',primitive_boundary='raw_eq/transmute and primitive scalar equality retain their existing Rust semantics/compiler-cohort boundary D381/D386; no LLVM or binary law is added',qualification='source identity of complete reached runtime method bodies; const impl grammar moves between versions; no new checker credited as original')
(D/'resume-v216-original-route/source-binding.json').write_text(json.dumps(out,indent=2)+'\n');print(identity)
