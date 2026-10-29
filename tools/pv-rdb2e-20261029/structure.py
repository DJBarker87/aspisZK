"""Exact body-token binding; listed substitutions never receive semantics credit here."""
from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2e-20261029';N=E/'native'
def tokens(s):
 return [m.group() for m in re.finditer(r'"(?:\\.|[^"\\])*"|//[^\n]*|/\*.*?\*/|[A-Za-z_][A-Za-z0-9_]*|0x[0-9A-Fa-f_]+|[0-9]+(?:[ui][0-9]+)?|::|->|=>|\S',s,re.S) if not m.group().startswith(('//','/*'))]
def body(s,name):
 t=tokens(s);i=next(i for i in range(len(t)-1)if t[i:i+2]==['fn',name]);a=t.index('{',i);d=1;b=a+1
 while d:
  if t[b]=='{':d+=1
  if t[b]=='}':d-=1
  b+=1
 return t[a:b]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
checks=[]
for old,new in [('sha256-soft.rs','soft.rs'),('sha256-x86.rs','x86.rs'),('sha-consts.rs','consts.rs')]:
 a=E/'source'/old;b=N/new;checks.append(dict(original=str(a.relative_to(E)),owned=str(b.relative_to(E)),original_sha256=sha(a),owned_sha256=sha(b),byte_equal=a.read_bytes()==b.read_bytes()))
a=(E/'source/sha-core-api.rs').read_text();b=(N/'main.rs').read_text()
original=body(a,'finalize_variable_core');owned=body(b,'finalize')
source=' '.join(original).replace('Self :: BlockSize :: U64','64u64')
assert tokens(source)==owned
checks.append(dict(body='Sha256VarCore::finalize_variable_core',same_calls_same_order_same_error_paths=True,exact_substitutions=[dict(source='Self::BlockSize::U64',owned='64u64',reason='fixed U64 block size; constant law in Lean required')],source_tokens_sha256=hashlib.sha256('\0'.join(original).encode()).hexdigest(),owned_tokens_sha256=hashlib.sha256('\0'.join(owned).encode()).hexdigest()))
original=body((E/'source/sha256.rs').read_text(),'compress256');owned=body(b,'compress256');source=' '.join(original).replace('compress (','x86 :: compress (');assert tokens(source)==owned
checks.append(dict(body='sha256::compress256',substitution='selected compress alias → x86::compress; selected by x86_64, no force-soft/force-soft-compact/asm',source_tokens_sha256=hashlib.sha256('\0'.join(original).encode()).hexdigest()))
assert all(c.get('byte_equal',True) for c in checks)
r=dict(checks=checks,source_model_binding='partial; Rust-copy body identity does not prove Lean source projection or hardware intrinsic adequacy',class_if_completed='structural (K-1 substitute)',selection=dict(sha2='0.10.9',features=['default','std'],architecture='x86_64-unknown-linux-gnu',profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind',rule='all four target features compile-time enabled => true; otherwise Linux CPUID cached using relaxed AtomicU8: leaf1.edx[26] SSE2 & leaf1.ecx[9] SSSE3 & leaf1.ecx[19] SSE4.1 & leaf7/subleaf0.ebx[29] SHA. true => digest_blocks; false => soft::compress. Cache initially255;0=false;1=true.',reachable=['sha256/x86.rs::digest_blocks','sha256/soft.rs::compress'],sha_ni_owner_pending=True),composition_trust='reclassification within existing tool trust, never premise removal')
(E/'structural-binding.json').write_text(json.dumps(r,indent=2));print('PASS exact copied source and fixed-type body token bindings; no universal native/Lean credit')
