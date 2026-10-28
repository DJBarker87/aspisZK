"""Exact source-body transport, including typed impl and integer macro invocation.
No new extraction checker is substituted for an original gate.
"""
from pathlib import Path
import json,re,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028');O=D/'resume-v212';out=[]
def sha(b):return hashlib.sha256(b).hexdigest()
def tokens(s):
 s=re.sub(r'//[^\n]*|/\*.*?\*/','',s,flags=re.S)
 return re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]',s)
def body(s,marker):
 assert s.count(marker)==1,(marker,s.count(marker))
 a=s.index(marker);b=s.index('{',a);depth=1;e=b+1
 while depth:
  depth+=(s[e]=='{')-(s[e]=='}');e+=1
 return s[a:e]
for version in ['nightly-2026-06-01','1.94.1']:
 root=Path('/home/dombarker/.rustup/toolchains')/(version+'-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src')
 rec=dict(toolchain=version,files={},bodies={})
 for f in ['option.rs','num/uint_macros.rs','num/mod.rs','convert/num.rs']:
  p=root/f;s=p.read_text();rec['files'][f]=dict(path=str(p),sha256=sha(p.read_bytes()))
  if f=='option.rs':
   for n in ['fn branch(self) -> ControlFlow<Self::Residual, Self::Output>','fn from_residual(residual: Option<convert::Infallible>) -> Self']:
    v=body(s,n);rec['bodies'][n]=dict(text=v,token_sha256=sha('\0'.join(tokens(v)).encode()))
   assert ('impl<T> const ops::FromResidual<Option<convert::Infallible>> for Option<T>' if version=='1.94.1' else 'const impl<T> ops::FromResidual<Option<convert::Infallible>> for Option<T>') in s
  elif f=='num/uint_macros.rs':
   for n in ['wrapping_add','wrapping_sub','wrapping_mul','wrapping_shr']:
    v=body(s,'pub const fn '+n+'(');rec['bodies'][n]=dict(text=v,token_sha256=sha('\0'.join(tokens(v)).encode()))
   v=body(s,'pub const unsafe fn unchecked_shr(self, rhs: u32) -> Self')
   rec['bodies']['unchecked_shr']=dict(text=v,token_sha256=sha('\0'.join(tokens(v)).encode()),precondition_law='R1Z.PV_RDCD_ShiftBound.mask_bound')
  elif f=='convert/num.rs':
   marker='fn from(small: $Small) -> Self' if version=='1.94.1' else 'fn from(small: $small) -> Self'
   v=body(s,marker);runtime=v
   if version!='1.94.1':
    runtime='\n'.join(line for line in runtime.splitlines() if 'debug_assert!(' not in line).replace('$small','$Small').replace('$large','$Large')
   rec['bodies']['FromU32U64_macro_body']=dict(text=v,release_body=runtime,token_sha256=sha('\0'.join(tokens(runtime)).encode()),law='R1Z.PV_RDCD_Cast194.binding',qualification='old debug_assert lines disabled under recorded release profile; new deployed body is the primitive cast')
   assert 'impl_from!(u32 => u64,' in s
  else:
   for ty in ['u32','u64']:
    a=s.index('impl '+ty+' {');b=s.index('uint_impl!',a);brace=s.index('{',b);e=brace+1;depth=1
    while depth:
     depth+=(s[e]=='{')-(s[e]=='}');e+=1
    v=s[b:e];assert 'Self = '+ty in v and 'ActualT = '+ty in v
    rec['bodies']['uint_impl! '+ty]=dict(text=v,token_sha256=sha('\0'.join(tokens(v)).encode()))
 out.append(rec)
# Whole macro arguments include docs for unrelated new carryless methods.
for c in out:
 for ty,bits in [('u32',32),('u64',64)]:
  text=c['bodies']['uint_impl! '+ty]['text']
  assert re.search(r'\b'+ty+r'\s*,',text) and re.search(r'\b'+str(bits)+r'\s*,',text),(ty,text)
  c['bodies']['reached macro binding '+ty]=dict(text=ty+':BITS='+str(bits),token_sha256=sha((ty+':BITS='+str(bits)).encode()))
comparisons={k:out[0]['bodies'][k]['token_sha256']==out[1]['bodies'][k]['token_sha256'] for k in out[0]['bodies']}
result=dict(cohorts=out,identical= comparisons,qualification='Exact typed Option methods and selected wrapping method bodies; macro invocation difference must be reviewed before whole-row transfer. Rust intrinsic semantics remain a compiler boundary, no intrinsic implementation is proved by this source comparison.')
(O/'std-complete-binding.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(comparisons,indent=2))
