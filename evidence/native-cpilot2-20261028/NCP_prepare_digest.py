from pathlib import Path
import NCP_runner as m
import subprocess,json,difflib
m.admit('NCP_DIGEST_UPLOAD')
# Retain the exact annotation-only instrumentation patch; frozen bodies unchanged.
relative='crates/aspis-statement/src/atomic_statement.rs'
s=subprocess.check_output(['git','show',m.REV+':'+relative],text=True)
s=s.replace('pub fn encode_digest_canonical(', '#[cfg_attr(kani, kani::ensures(|r: &[u8;32]| *r == crate::NCP_digest::NCP_ref_encode(digest)))]\npub fn encode_digest_canonical(')
s=s.replace('pub fn decode_digest_canonical(', '#[cfg_attr(kani, kani::ensures(|r: &Result<Digest,AtomicStatementError>| *r == crate::NCP_digest::NCP_ref_decode(bytes)))]\npub fn decode_digest_canonical(')
# Reference decoder has eight explicit short-circuit steps, matching its cohort law.
p=m.E/'NCP_digest.rs.txt';x=p.read_text();start=x.index(' let mut d=[M31(0);8]');end=x.index('\n}',start)
x=x[:start]+''.join(f' let x{i}=(b[{4*i}] as u32)|((b[{4*i+1}] as u32)<<8)|((b[{4*i+2}] as u32)<<16)|((b[{4*i+3}] as u32)<<24);if x{i}>=2147483647{{return Err(AtomicStatementError::NonCanonicalDigest)}}\n' for i in range(8))+' Ok(['+','.join(f'M31(x{i})' for i in range(8))+'])'+x[end:];p.write_text(x)
# Encoding proof_for_contract is pending: native loop requires a permitted inductive contract route.
# The module contains its proposed harness, but it is NOT submitted by this script.
files={relative:s,'crates/aspis-statement/src/NCP_digest.rs':x}
r=m.py(f'''from pathlib import Path
import json
src=Path({(m.B+'/NCP_src')!r})
for n,s in {files!r}.items():(src/n).write_text(s)
p=src/'crates/aspis-statement/src/lib.rs';s=p.read_text();assert 'pub mod NCP_digest' not in s;p.write_text(s+'\\n#[cfg(kani)] pub mod NCP_digest;\\n')
''');assert r.returncode==0,r.stderr
# full patch collector populated later, after all harness-only instrumentation.
