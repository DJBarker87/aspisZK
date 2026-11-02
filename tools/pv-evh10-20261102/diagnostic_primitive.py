"""Source control binding for FileDesc/cvt; actual primitive association OPEN."""
from pathlib import Path
import json,subprocess,hashlib,shlex,sys
E=Path('evidence/pv-evh10-20261102');sha=lambda b:hashlib.sha256(b).hexdigest()
root='/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/std/src/'
anchors=[('sys/fd/unix.rs','pub fn write(&self, buf: &[u8])','body'),
 ('sys/fd/unix.rs','const READ_LIMIT: usize','const'),
 ('sys/pal/unix/mod.rs','macro_rules! impl_is_minus_one','body'),
 ('sys/pal/unix/mod.rs','pub fn cvt<T: IsMinusOne>','body'),
 ('io/error.rs','pub fn last_os_error()','body'),
 ('io/error.rs','pub fn from_raw_os_error(code: RawOsError)','body')]
code=r'''from pathlib import Path
import sys,json,hashlib
x=json.load(sys.stdin);out=[]
for path,anchor,kind in x['anchors']:
 p=Path(x['root']+path);raw=p.read_bytes();s=raw.decode();a=s.index(anchor)
 if kind=='const':j=s.index('\n};',a)+3
 else:
  i=s.index('{',a);j=i+1;n=1
  while n:
   n+=(s[j]=='{')-(s[j]=='}');j+=1
 out.append(dict(path=path,anchor=anchor,file_sha256=hashlib.sha256(raw).hexdigest(),text=s[a:j]))
print(json.dumps(out))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(dict(root=root,anchors=anchors)),text=True,capture_output=True);assert r.returncode==0,r.stderr
rows=json.loads(r.stdout);write,limit,minus,cvt,last,ctor=[x['text'] for x in rows]
for x in ['libc::write(', 'self.as_raw_fd()', 'buf.as_ptr() as *const libc::c_void', 'cmp::min(buf.len(), READ_LIMIT)', 'Ok(ret as usize)']:assert x in write
assert 'libc::ssize_t::MAX as usize' in limit and '*self == -1' in minus
assert 'if t.is_minus_one() { Err(io::Error::last_os_error()) } else { Ok(t) }' in cvt
assert 'Error::from_raw_os_error(sys::os::errno())' in last
out=dict(evidence_class='structural own-1 source-control association; incomplete primitive/native diagnostic fidelity',sources=rows,
 mapping=['FileDesc passes original fd, buffer address and min(length,READ_LIMIT) to libc::write','cvt checks precisely -1; last_os_error executes only in that branch and after the raw write','nonerror raw return is cast to usize64 by modulo 2^64, not Int.toNat','existing write_all Driver now carries suffix addresses derived from the original literal pointer; interrupted/drop/WriteZero/bad-count remain WORLD operations'],
 retained=['actual libc signed64 ABI and write footprint/delivery/errno world association','original literal address/provenance and valid extent','TLS errno read and io::Error/Repr representation/from_raw_os_error/drop source association','EBADF/ErrorKind actual classification, locks/RefCell/guard/hook and all seven callback installations','allocator metadata/ValidAnswer/Global/System and complete native entry','L3 joint observation, V370/V371, D520/U/D524 and all endpoint/deployment conditions'],trust_fields_added=[],rows_removed=[])
p=E/'diagnostic-primitive-binding.json'
if '--check' in sys.argv:assert json.load(open(p))==out
else:p.write_text(json.dumps(out,indent=2)+'\n')
print('PASS FileDesc/cvt source control; actual libc/errno/error/native binding OPEN')
