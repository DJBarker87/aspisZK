"""Read and pin the selected nightly stdlib; check V175's wrapper chain only."""
from pathlib import Path
import subprocess,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-fxio-20261028'
H='dombarker@100.108.41.90'
code='''import json,hashlib
from pathlib import Path
r=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
print(json.dumps({p:dict(path=str(r/p),sha256=hashlib.sha256((r/p).read_bytes()).hexdigest(),text=(r/p).read_text()) for p in ['std/src/fs.rs','std/src/sys/fs/unix.rs','std/src/io/error.rs']}))
'''
r=subprocess.run(['ssh',H,'python3','-'],input=code,text=True,capture_output=True)
assert r.returncode==0,r.stderr
j=json.loads(r.stdout)
checks={
 'OpenOptions.open delegates to _open(path.as_ref)': 'self._open(path.as_ref())' in j['std/src/fs.rs']['text'],
 '_open delegates to platform File.open and preserves Result.map': 'fs_imp::File::open(path, &self.0).map(|inner| File { inner })' in j['std/src/fs.rs']['text'],
 'platform File.open delegates through C path': 'run_path_with_cstr(path, &|path| File::open_c(path, opts))' in j['std/src/sys/fs/unix.rs']['text'],
 'open_c uses creation flags': '| opts.get_creation_mode()?' in j['std/src/sys/fs/unix.rs']['text'],
 'open_c reaches open64 with flags/mode and propagates error': 'let fd = cvt_r(|| unsafe { open64(path.as_ptr(), flags, opts.mode as c_int) })?;' in j['std/src/sys/fs/unix.rs']['text'],
 'create_new selects O_CREAT and O_EXCL': '(false, false, true) | (true, false, true) | (false, true, true) | (true, true, true)' in j['std/src/sys/fs/unix.rs']['text'] or '(_, _, true) => Ok(libc::O_CREAT | libc::O_EXCL)' in j['std/src/sys/fs/unix.rs']['text'],
 'Error.kind decodes OS errno': 'ErrorData::Os(code) => sys::io::decode_error_kind(code)' in j['std/src/io/error.rs']['text'],
}
for p,x in j.items():
 text=x.pop('text');dst=p.replace('/','_')+'.txt';(E/dst).write_text(text);x['evidence_path']=dst
out=dict(toolchain='nightly-2026-06-01',files=j,checks=checks,ok=all(checks.values()),evidence_class='structural source inspection, not a universal OS primitive proof',scope='V175 wrapper to open64, plus Error.kind OS branch; no closure credit for other rows')
(E/'stdlib-structural.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
assert out['ok']
